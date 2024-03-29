ARG K_COMMIT
FROM runtimeverificationinc/kframework-k:ubuntu-bionic-${K_COMMIT}

ENV TZ=America/Chicago
RUN    ln --symbolic --no-dereference --force /usr/share/zoneinfo/$TZ /etc/localtime \
    && echo $TZ > /etc/timezone

RUN    apt update                                                          \
    && apt upgrade --yes                                                   \
    && apt install --yes                                                   \
           boogie                                                          \
           llvm-8                                                          \
           ninja-build                                                     \
           python3                                                         \
           python3-pip                                                     \
           kakoune vim

ARG USER_ID=1000
ARG GROUP_ID=1000
RUN    groupadd --gid $GROUP_ID user                                        \
    && useradd --create-home --uid $USER_ID --shell /bin/sh --gid user user
USER $USER_ID:$GROUP_ID

ADD --chown=user . /home/user/boogie/
WORKDIR /home/user/boogie/

ENV LC_ALL=C.UTF-8
