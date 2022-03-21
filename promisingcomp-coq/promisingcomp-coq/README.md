# Verifying Optimizations of Concurrent Programs in the Promising Semantics

This project mechanizes the proofs of the verification framework shown in Figure 3 in our paper in the Coq proof assistant. You can build the project by the following instructions.

## Usage

- Requirement: opam (>=2.0.0), Coq 8.13.1
- Install dependencies with opam

```
./configure
make build -j
# clean
make clean
```



<!-- ### docker 

```
docker build -t compoptcert:1.0 .
sudo docker build -t compoptcert:1.0 --build-arg http_proxy=<proxy> --build-arg https_proxy=<proxy> .
sudo docker run -it -p 52022:22 --name compoptcert:1.0 compoptcert
docker save -o compoptcert-image.tar compoptcert:1.0
docker import  compoptcert-image.tar compoptcert:1.0
``` -->