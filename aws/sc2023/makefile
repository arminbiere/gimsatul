build:
	docker build -t satcomp-gimsatul .
test: build
	./run.sh prime2209.cnf
	./run.sh prime4294967297.cnf
clean:
	rm -f `cat .gitignore`
