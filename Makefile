all: build copy
pypy: pypybuild pypycopy
both: all pypy

build: yicesfull.c setup.py
	python setup.py build || rm -rf build

copy: build
	rm -f yicesfull.so
	cp `find build -name yicesfull.so` .
	rm -rf build

pypybuild: yicesfull.c setup.py
	pypy setup.py build || rm -rf build

pypycopy: pypybuild
	rm -f yicesfull.pypy*.so
	cp `find build -name "yicesfull.pypy*"` .
	rm -rf build

clean:
	rm -rf build
	rm -f yicesfull.pypy*.so
	rm -f yicesfull.so
