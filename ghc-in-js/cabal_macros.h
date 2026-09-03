/* aeson is not a dependency of this build, so ghcjs-base's version test for
   it must resolve to "absent". GHC supplies the rest of the MIN_VERSION_*
   macros itself, so defining any of them here would collide. */
#ifndef MIN_VERSION_aeson
#define MIN_VERSION_aeson(a,b,c) 0
#endif
#ifndef MIN_VERSION_vector
#define MIN_VERSION_vector(a,b,c) 0
#endif
#ifndef MIN_VERSION_scientific
#define MIN_VERSION_scientific(a,b,c) 0
#endif
#ifndef MIN_VERSION_unordered_containers
#define MIN_VERSION_unordered_containers(a,b,c) 0
#endif
#ifndef MIN_VERSION_attoparsec
#define MIN_VERSION_attoparsec(a,b,c) 0
#endif
#ifndef MIN_VERSION_dlist
#define MIN_VERSION_dlist(a,b,c) 0
#endif
#ifndef MIN_VERSION_hashable
#define MIN_VERSION_hashable(a,b,c) 0
#endif
#ifndef MIN_VERSION_primitive
#define MIN_VERSION_primitive(a,b,c) 0
#endif
