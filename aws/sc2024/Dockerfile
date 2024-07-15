FROM satcomp-infrastructure:leader
USER root
ARG DEBIAN_FRONTEND=noninteractive
RUN apt-get update && apt-get -y upgrade
RUN apt-get install --no-install-recommends -y apt-utils
RUN apt-get install -y git make gcc
RUN git clone --branch sc2023 https://github.com/arminbiere/gimsatul
WORKDIR gimsatul
RUN ./configure -q && make
COPY solver /competition/solver
RUN chmod +x /competition/solver
