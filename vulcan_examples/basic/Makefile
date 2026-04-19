CXX = g++
CXXFLAGS = -std=c++20 -I./libvulcan/include

LIB_SRCS = libvulcan/src/vulcan.cpp libvulcan/src/feature_registry.cpp libvulcan/src/feature_store.cpp
LIB_OBJS = $(LIB_SRCS:.cpp=.o)

all: template

template: template.cpp $(LIB_OBJS)
	$(CXX) $(CXXFLAGS) -o $@ template.cpp $(LIB_OBJS)

libvulcan/src/%.o: libvulcan/src/%.cpp
	$(CXX) $(CXXFLAGS) -c $< -o $@

clean:
	rm -f template $(LIB_OBJS)
