# I maintain a homebrew tap [1], so I often find myself writing Homebrew
# "formulae" to build and package useful software.  There are MANY tools
# available to formula authors that are not documented in the official Homebrew
# Formula Cookbook [2].  In my opinion some of these are ABSOLUTE NECESSITIES
# and I document them here as I discover them.
#
# [1]: https://github.com/Calvin-L/homebrew-tap
# [2]: https://docs.brew.sh/Formula-Cookbook

class HomebrewFormulae < Formula
  desc "Useful description"
  homepage "https://example.com"
  version "1.8.0"
  # revision 1 # https://docs.brew.sh/Formula-Cookbook#formulae-revisions
  license "MIT" # https://spdx.org/licenses/


  # ------------------------------- Downloading sources

  # Direct URL ==> Homebrew can infer the `version` from this.
  url "https://github.com/Calvin-L/many-smt/archive/refs/tags/v1.0.0.tar.gz"

  # Direct URL that references `version`.  I like this style a little better,
  # but it's entirely a matter of taste.
  url "https://github.com/Calvin-L/many-smt/archive/refs/tags/v#{version}.tar.gz"

  # %XX escape codes are legal in URLs, e.g.
  url "https://cgi.csc.liv.ac.uk/%7Ekonev/software/trp++/translator/translate.tar.bz2"

  # Git revision ==> You need to specify `version` manually and you do not need
  # to provide `sha256`.
  url "https://github.com/tlaplus/tlaplus.git", revision: "77bb1c7301d93a4f8c8dedc2b4f26f1e8843ecc2"

  # Compute this once with `curl -Lf 'URL' | shasum -a 256`.
  sha256 "b33902cb95edb437e453c81501cd8251290a3d9b748d9d4e83a40736fde2705f"


  # ------------------------------- Declaring dependencies

  depends_on "java"
  depends_on "ant" => :build
  depends_on "openjdk" => [:build, :test]

  # Flags you can use here:
  #   - (no flags)   -- build-, test-, and run-time
  #   - :build       -- build-time only
  #   - :test        -- test-time only
  #   - :optional    -- adds `--with-packagename` flag, dependency is NOT installed by default
  #   - :recommended -- adds `--without-packagename` flag, dependency IS installed by default


  # ------------------------------- Compiling/installing

  def install

    # Useful paths you can use in here:
    #  - `prefix`  -- where you should install stuff
    #  - `bin`     -- usually equals prefix/"bin"
    #  - `lib`     -- usually equals prefix/"lib"
    #  - `libexec` -- usually equals prefix/"libexec"
    
    # Common shellisms have dedicated functions:
    cd "tlatools/org.lamport.tlatools"
    rm_r "dir"
    mkdir_p bin
    cp "exe", bin
    cp_r "path", lib
    chmod 0755, bin/"exe"

    # Shorthand for "cp to bin; chmod 0555"
    bin.install "exe"

    # You can also change the name of a file as you install it to bin:
    bin.install "filename" => "exename"

    # Invoking a standard autotools configure script:
    system "./configure", *std_configure_args

    # Referencing the install paths of other formulae --- this is great if you
    # want to isolate installed products from the user's environment or if you
    # need to point a configure script at some specific path.
    inreplace "etc/settings", "/path/to/java/bin", Formula["java"].bin

    # In general, you can use:
    #   - Formula["name"].prefix
    #   - Formula["name"].bin
    #   - Formula["name"].lib

    # Create a file at build time
    (bin/exe).write("#!/bin/bash\nexec java -XX:+UseParallelGC -DTLA-Library=\"$TLA_PATH\" -cp '#{lib}/tla2tools.jar' Classname \"$@\"\n")
    chmod 0555, bin/exe

    # Modifying the environment --- this affects all subsequent commands.
    ENV["VARIABLE_NAME"] = "VALUE"

    # Colon-separated lists of paths are very common in environment variables
    # (e.g. PATH, CLASSPATH, etc).  Homebrew offers a utility for extending
    # those lists:
    ENV.prepend_path "OCAMLPATH", Formula["coq"].lib

    # Managing parallelism --- Homebrew turns on `make` parallelism by default
    # using environment variables, but some packages cannot be consistently
    # compiled in parallel.
    jobs = ENV.make_jobs  # capture how much parallelism Homebrew recommends
    ENV.deparallelize     # turn off parallel `make`


    # ------------------------------- Python-specific advice

    # Use `brew create --python [pypi url]`.  This will include useful install
    # lines like:
    python = Formula["python@3"]
    system python.opt_libexec/"bin"/"python", *Language::Python.setup_install_args(prefix, python)


    # ------------------------------- Java-specific advice

    # You'll probably want
    # depends_on "java"
    # depends_on "maven" # or "ant" or "gradle"
    # depends_on "openjdk" => :build
    ENV["JAVA_HOME"] = Formula["openjdk"].libexec/"openjdk.jdk"/"Contents"/"Home"

  end

  test do
    # `test do` will create, run in and delete a temporary directory.
    #
    # The installed folder is not in the path, so use the entire path to any
    # executables being tested: `system "#{bin}/program", "do", "something"`.
    (testpath/"Test.tla").write("---- MODULE Test ----\nEXTENDS Integers\nCONSTANT MAX\nVARIABLES x\nInit == x=1\nNext == x < MAX /\\ x' = x + 1\n======\n")
    (testpath/"Test.cfg").write("CONSTANT MAX = 10\nINIT Init\nNEXT Next\n")
    system bin/"tlc2", "-deadlock", "-workers", "auto", "Test"
  end
end
