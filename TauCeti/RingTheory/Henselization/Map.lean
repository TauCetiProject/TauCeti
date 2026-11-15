/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Henselization.Henselian
public import TauCeti.RingTheory.Henselization.Lift

/-!
# Functoriality of the henselization of a pair

A map of pairs `f : (R, I) → (S, J)`, that is a ring map `f : R → S` with `f(I) ⊆ J`, induces a
ring map `Henselization.map f hf` from the henselization of `(R, I)` to the henselization of
`(S, J)`. It is obtained from the universal property of the henselization of `(R, I)`, applied
to the henselian pair `(algebra J, extended J)`, and it is the unique ring map compatible with
`f` and the structure maps. Consequently the construction is functorial, carries the extended
ideal into the extended ideal, and is compatible with the identification of the closed fibres
`R ⧸ I ≅ algebra I ⧸ extended I`.

## Main results

* `TauCeti.Henselization.map`: the ring map of henselizations induced by a map of pairs.
* `TauCeti.Henselization.map_unique`: `map f hf` is the unique ring map compatible with `f`.
* `TauCeti.Henselization.map_id`, `TauCeti.Henselization.map_comp`,
  `TauCeti.Henselization.map_map`: functoriality.
* `TauCeti.Henselization.quotientMap_comp_reducedMap`: the identification of the closed fibres is
  natural.

## References

* [Stacks Project, Lemma 15.12.1](https://stacks.math.columbia.edu/tag/0A02), the universal
  property of the henselization of a pair, from which the functoriality follows.
-/

public section

universe u v w

namespace TauCeti.Henselization

variable {R : Type u} [CommRing R] {I : Ideal R}

variable {S : Type v} [CommRing S] {J : Ideal S}

/-- The ring map from the henselization of `(R, I)` to the henselization of `(S, J)` induced by
a map of pairs, that is a ring map `f : R → S` with `f(I) ⊆ J`. It is the unique ring map
compatible with `f` and the structure maps (`map_unique`). -/
noncomputable def map (f : R →+* S) (hf : I.map f ≤ J) : algebra I →+* algebra J :=
  letI : Algebra R (algebra J) := ((algebraMap S (algebra J)).comp f).toAlgebra
  (lift (I := I) (J := extended J) (by
    rw [RingHom.algebraMap_toAlgebra, ← Ideal.map_map]
    exact Ideal.map_mono hf)).toRingHom

/-- The map of henselizations is compatible with the structure maps. -/
@[simp]
theorem map_algebraMap (f : R →+* S) (hf : I.map f ≤ J) (r : R) :
    map f hf (algebraMap R (algebra I) r) = algebraMap S (algebra J) (f r) := by
  let : Algebra R (algebra J) := ((algebraMap S (algebra J)).comp f).toAlgebra
  exact AlgHom.commutes _ r

/-- The map of henselizations is compatible with the structure maps, as an equality of ring
maps. -/
@[simp]
theorem map_comp_algebraMap (f : R →+* S) (hf : I.map f ≤ J) :
    (map f hf).comp (algebraMap R (algebra I)) = (algebraMap S (algebra J)).comp f :=
  RingHom.ext (map_algebraMap f hf)

/-- The map of henselizations carries the extended ideal of `(R, I)` into the extended ideal of
`(S, J)`. -/
theorem map_extended_le (f : R →+* S) (hf : I.map f ≤ J) :
    (extended I).map (map f hf) ≤ extended J := by
  rw [extended, Ideal.map_map, map_comp_algebraMap, ← Ideal.map_map]
  exact Ideal.map_mono hf

/-- **Uniqueness of the map of henselizations.** A ring map between henselizations compatible
with a map of pairs `f` and the structure maps is `map f hf`. -/
theorem map_unique (f : R →+* S) (hf : I.map f ≤ J) (g : algebra I →+* algebra J)
    (hg : g.comp (algebraMap R (algebra I)) = (algebraMap S (algebra J)).comp f) :
    g = map f hf :=
  ringHom_ext_of_map_le_jacobson (hg.trans (map_comp_algebraMap f hf).symm) (by
    rw [hg, ← Ideal.map_map]
    exact (Ideal.map_mono hf).trans (extended_le_jacobson J))

/-- The identity map of pairs induces the identity of the henselization. -/
@[simp]
theorem map_id : map (RingHom.id R) (Ideal.map_id I).le = RingHom.id (algebra I) :=
  (map_unique _ _ _ (by rw [RingHom.id_comp, RingHom.comp_id])).symm

/-- The map of henselizations induced by a composite of maps of pairs is the composite of the
induced maps. -/
theorem map_comp {T : Type w} [CommRing T] {K : Ideal T} (g : S →+* T) (f : R →+* S)
    (hg : J.map g ≤ K) (hf : I.map f ≤ J) :
    map (g.comp f) ((Ideal.map_map f g).symm.trans_le ((Ideal.map_mono hf).trans hg)) =
      (map g hg).comp (map f hf) :=
  (map_unique _ _ _ (RingHom.ext fun r ↦ by simp)).symm

/-- Applying the maps of henselizations induced by two composable maps of pairs in turn is
applying the map induced by their composite. -/
@[simp]
theorem map_map {T : Type w} [CommRing T] {K : Ideal T} (g : S →+* T) (f : R →+* S)
    (hg : J.map g ≤ K) (hf : I.map f ≤ J) (x : algebra I) :
    map g hg (map f hf x) =
      map (g.comp f) ((Ideal.map_map f g).symm.trans_le ((Ideal.map_mono hf).trans hg)) x := by
  rw [map_comp, RingHom.comp_apply]

/-- **Naturality of the closed fibre.** The identifications `R ⧸ I ≅ algebra I ⧸ extended I` of
`quotient_bijective` are compatible with the maps induced by a map of pairs `f` on the quotients
and on the henselizations. -/
theorem quotientMap_comp_reducedMap (f : R →+* S) (hf : I.map f ≤ J) :
    (Ideal.quotientMap (extended J) (map f hf)
        (Ideal.map_le_iff_le_comap.mp (map_extended_le f hf))).comp (reducedMap I (algebra I)) =
      (reducedMap J (algebra J)).comp
        (Ideal.quotientMap J f (Ideal.map_le_iff_le_comap.mp hf)) := by
  apply Ideal.Quotient.ringHom_ext
  ext r
  simp

-- The identity of `(𝔽₅, 0)` induces the identity of its henselization, computed on `1`.
example : map (RingHom.id (ZMod 5)) (I := ⊥) (J := ⊥) (by simp) 1 = 1 := by
  simp

-- Reduction `ℤ → 𝔽₅` sends `7` in the henselization of `(ℤ, 0)` to `2`.
example : map (Int.castRingHom (ZMod 5)) (I := ⊥) (J := ⊥) (by simp)
    (algebraMap ℤ (algebra (⊥ : Ideal ℤ)) 7) = algebraMap (ZMod 5) (algebra ⊥) 2 := by
  rw [map_algebraMap, show Int.castRingHom (ZMod 5) 7 = 2 by decide]

-- The identity of `(ℤ/9, (3))` induces a map of henselizations fixing `1`.
example : map (RingHom.id (ZMod 9)) (I := Ideal.span {3}) (J := Ideal.span {3}) (by simp) 1 = 1 :=
  by simp

-- The map of henselizations induced by `(ℤ, 0) → (ℤ/5, 0)` is not injective: it kills `5`, which
-- is nonzero in the henselization of `(ℤ, 0)`, namely `ℤ` itself.
example : ¬ Function.Injective
    (map (Int.castRingHom (ZMod 5)) (I := ⊥) (J := ⊥) (by simp)) := by
  intro h
  have h5 : algebraMap ℤ (algebra (⊥ : Ideal ℤ)) 5 = 0 := (injective_iff_map_eq_zero _).mp h _ <| by
    rw [map_algebraMap, show Int.castRingHom (ZMod 5) 5 = 0 by decide, map_zero]
  rw [map_eq_zero_iff _ (bijective_algebraMap_of_henselianRing ⊥).1] at h5
  norm_num at h5

end TauCeti.Henselization
