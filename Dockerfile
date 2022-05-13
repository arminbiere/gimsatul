FROM ubuntu:20.04
ARG DEBIAN_FRONTEND=noninteractive
RUN apt-get update && apt-get -y upgrade
RUN apt-get install --no-install-recommends -y apt-utils
RUN apt-get install -y git make gcc 
COPY . /opt/gimsatul
WORKDIR /opt/gimsatul
RUN ./configure && make
ENTRYPOINT ["./run-in-docker.sh"]