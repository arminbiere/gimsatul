FROM gimsatul-base AS builder
USER root
FROM satcomp-base:leader AS gimsatul_liaison
WORKDIR /
COPY --from=builder /gimsatul/gimsatul gimsatul
COPY --chown=ecs-user /run_gimsatul.sh /competition
COPY --chown=ecs-user /solver /competition
USER ecs-user
RUN chmod +x /competition/run_gimsatul.sh
RUN chmod +x /competition/solver
