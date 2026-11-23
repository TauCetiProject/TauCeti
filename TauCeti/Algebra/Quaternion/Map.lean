/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Quaternion

/-!
# Coefficientwise maps of quaternion algebras

A ring homomorphism `f : R →+* S` acts on quaternions coordinatewise.

## Main definitions

* `TauCeti.QuaternionAlgebra.map`: the ring homomorphism `ℍ[R,a,b,c] →+* ℍ[S,a',b',c']` applying
  `f` to each coordinate, for any target parameters with `f a = a'`, `f b = b'` and `f c = c'`.
* `Quaternion.map`: its instance `ℍ[R] →+* ℍ[S]` for the Hamilton quaternions.
-/

public section

open scoped Quaternion

namespace TauCeti.QuaternionAlgebra

variable {R S : Type*} [CommRing R] [CommRing S] {a' b' c' : S}

/-- Apply a ring homomorphism to the coefficients of a quaternion. The target parameters are
any `a' b' c'` with `f a = a'`, `f b = b'` and `f c = c'`, so that the map can land, for example,
in `ℍ[S]` itself rather than in `ℍ[S,f (-1),f 0,f (-1)]`. -/
def map (a b c : R) (f : R →+* S) (ha : f a = a') (hb : f b = b') (hc : f c = c') :
    ℍ[R,a,b,c] →+* ℍ[S,a',b',c'] where
  toFun q := ⟨f q.re, f q.imI, f q.imJ, f q.imK⟩
  map_zero' := by ext <;> simp
  map_one' := by ext <;> simp
  map_add' x y := by ext <;> simp
  map_mul' x y := by subst ha hb hc; ext <;> simp

variable (a b c : R) (f : R →+* S) (ha : f a = a') (hb : f b = b') (hc : f c = c')

@[simp]
theorem map_mk (w x y z : R) :
    map a b c f ha hb hc ⟨w, x, y, z⟩ = ⟨f w, f x, f y, f z⟩ := (rfl)

@[simp]
theorem re_map (q : ℍ[R,a,b,c]) : (map a b c f ha hb hc q).re = f q.re := (rfl)

@[simp]
theorem imI_map (q : ℍ[R,a,b,c]) : (map a b c f ha hb hc q).imI = f q.imI := (rfl)

@[simp]
theorem imJ_map (q : ℍ[R,a,b,c]) : (map a b c f ha hb hc q).imJ = f q.imJ := (rfl)

@[simp]
theorem imK_map (q : ℍ[R,a,b,c]) : (map a b c f ha hb hc q).imK = f q.imK := (rfl)

@[simp]
theorem map_star (q : ℍ[R,a,b,c]) :
    map a b c f ha hb hc (star q) = star (map a b c f ha hb hc q) := by
  subst hb
  ext <;> simp

@[simp]
theorem map_coe (r : R) : map a b c f ha hb hc (r : ℍ[R,a,b,c]) = (f r : ℍ[S,a',b',c']) := by
  ext <;> simp

@[simp]
theorem map_id : map a b c (RingHom.id R) rfl rfl rfl = RingHom.id ℍ[R,a,b,c] := (rfl)

@[simp]
theorem map_comp {T : Type*} [CommRing T] (g : S →+* T) {a'' b'' c'' : T}
    (ha' : g a' = a'') (hb' : g b' = b'') (hc' : g c' = c'') :
    (map a' b' c' g ha' hb' hc').comp (map a b c f ha hb hc) =
      map a b c (g.comp f) (by rw [RingHom.comp_apply, ha, ha'])
        (by rw [RingHom.comp_apply, hb, hb']) (by rw [RingHom.comp_apply, hc, hc']) := (rfl)

end TauCeti.QuaternionAlgebra

namespace Quaternion

variable {R S : Type*} [CommRing R] [CommRing S]

/-- Apply a ring homomorphism to the coefficients of a quaternion in `ℍ[R]`, landing in `ℍ[S]`:
the instance of `TauCeti.QuaternionAlgebra.map` at the parameters `-1, 0, -1`. -/
def map (f : R →+* S) : ℍ[R] →+* ℍ[S] :=
  TauCeti.QuaternionAlgebra.map (-1) 0 (-1) f (by rw [map_neg, map_one]) (map_zero f)
    (by rw [map_neg, map_one])

@[simp]
theorem map_mk (f : R →+* S) (w x y z : R) :
    map f (⟨w, x, y, z⟩ : ℍ[R]) = ⟨f w, f x, f y, f z⟩ := (rfl)

@[simp]
theorem re_map (f : R →+* S) (q : ℍ[R]) : (map f q).re = f q.re := (rfl)

@[simp]
theorem imI_map (f : R →+* S) (q : ℍ[R]) : (map f q).imI = f q.imI := (rfl)

@[simp]
theorem imJ_map (f : R →+* S) (q : ℍ[R]) : (map f q).imJ = f q.imJ := (rfl)

@[simp]
theorem imK_map (f : R →+* S) (q : ℍ[R]) : (map f q).imK = f q.imK := (rfl)

@[simp]
theorem map_star (f : R →+* S) (q : ℍ[R]) : map f (star q) = star (map f q) :=
  TauCeti.QuaternionAlgebra.map_star _ _ _ f _ _ _ q

@[simp]
theorem map_coe (f : R →+* S) (r : R) : map f (r : ℍ[R]) = (f r : ℍ[S]) :=
  TauCeti.QuaternionAlgebra.map_coe _ _ _ f _ _ _ r

@[simp]
theorem map_id : map (RingHom.id R) = RingHom.id ℍ[R] := (rfl)

@[simp]
theorem map_comp {T : Type*} [CommRing T] (f : R →+* S) (g : S →+* T) :
    (map g).comp (map f) = map (g.comp f) := (rfl)

end Quaternion
