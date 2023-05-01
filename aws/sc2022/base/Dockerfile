FROM satcomp-common-base-image
USER root
ARG DEBIAN_FRONTEND=noninteractive
RUN apt-get update && apt-get -y upgrade
RUN apt-get install --no-install-recommends -y apt-utils
RUN apt-get install -y git make gcc
RUN git clone https://github.com/arminbiere/gimsatul
WORKDIR gimsatul
RUN ./configure -q && make
