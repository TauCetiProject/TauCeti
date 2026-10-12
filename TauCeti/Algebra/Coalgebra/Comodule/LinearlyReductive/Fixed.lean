/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Algebra.Exact.Basic
public import TauCeti.Algebra.Coalgebra.Comodule.LinearlyReductive
import TauCeti.Algebra.Coalgebra.Subcomodule.Finite
import TauCeti.Algebra.Coalgebra.Subcomodule.Comap

/-!
# Exactness of invariants for linearly reductive coalgebras

The invariant-vector operation is exact for comodules over a linearly reductive coalgebra
with a distinguished element `1`. In particular, for a linearly reductive affine group,
every invariant vector in a quotient rational representation lifts to an invariant vector.
Neither the source nor the target representation needs to be finite dimensional.

The image statement is stronger than preservation of surjections: the image of the invariants
under any comodule morphism is the intersection of its image with the target invariants. Together
with preservation of injections, this gives exactness on short exact sequences. This is the
representation-theoretic input to descent of invariant functions in affine homogeneous spaces.

For a completely reducible source the same lifting, image, surjectivity, and exactness results
hold over a commutative ring, provided the coefficient coalgebra is flat. Over a field, local
finite dimensionality reduces an arbitrary lift to this case.

## References

* J. C. Jantzen, *Representations of Algebraic Groups*, I.2, invariants and exactness.
* W. C. Waterhouse, *Introduction to Affine Group Schemes*, §§3.2 and 16.3.
-/

public section

namespace TauCeti.Comodule

universe u v w x y

section Ring

variable {R : Type u} [CommRing R]
variable {C : Type v} [AddCommMonoid C] [Module R C] [Coalgebra R C] [One C]
  [Module.Flat R C]
variable {M : Type w} [AddCommMonoid M] [Module R M] [Comodule R C M]
variable {N : Type x} [AddCommMonoid N] [Module R N] [Comodule R C N]
variable {P : Type y} [AddCommMonoid P] [Module R P] [Comodule R C P]

/-- If the source is completely reducible, every invariant vector in the image of a comodule
morphism has an invariant preimage. Flatness of the coalgebra suffices over a general ring. -/
theorem Hom.exists_fixed_preimage_of_isCompletelyReducible (f : Hom R C M N)
    (hM : IsCompletelyReducible R C M) {n : N}
    (hn : n ∈ fixedSubcomodule R C N) (hnrange : n ∈ LinearMap.range f.toLinearMap) :
    ∃ m ∈ fixedSubcomodule R C M, f m = n := by
  let : AddCommGroup M := Module.addCommMonoidToAddCommGroup R
  let : AddCommGroup N := Module.addCommMonoidToAddCommGroup R
  obtain ⟨P, hP⟩ := hM.exists_isCompl (Hom.ker f)
  obtain ⟨m, hm⟩ := hnrange
  obtain ⟨a, ha, b, hb, hab⟩ :=
    Submodule.mem_sup.mp (hP.sup_eq_top ▸ (Submodule.mem_top : m ∈ (⊤ : Submodule R M)))
  have hfb : f b = n := by
    rw [← hm, ← hab, map_add]
    simp only [Hom.coe_toLinearMap, Hom.mem_ker.mp ha, zero_add]
  let : AddCommGroup P := Module.addCommMonoidToAddCommGroup R
  let i := f.comp P.subtype
  have hi : Function.Injective i := by
    have hdisj : Disjoint P.toSubmodule (LinearMap.ker f.toLinearMap) := by
      simpa only [← Hom.ker_toSubmodule] using hP.disjoint.symm
    intro z z' h
    apply Subtype.ext
    apply (LinearMap.disjoint_ker_iff_injOn.mp hdisj) z.property z'.property
    simpa only [i, Hom.comp_apply, Subcomodule.subtype_apply, Hom.coe_toLinearMap] using h
  have hbi : i (⟨b, hb⟩ : P) = n := by
    simpa [i] using hfb
  have hbfix : (⟨b, hb⟩ : P) ∈ fixedSubcomodule R C P :=
    (i.mem_fixedSubcomodule_iff_of_injective hi _).mp (hbi.symm ▸ hn)
  exact ⟨b, by simpa using P.subtype.mem_fixedSubcomodule hbfix, hfb⟩

omit [Module.Flat R C] in
private theorem Hom.map_fixedSubcomodule_of_fixed_preimage (f : Hom R C M N)
    (hLift : ∀ {n : N}, n ∈ fixedSubcomodule R C N →
      n ∈ LinearMap.range f.toLinearMap → ∃ m ∈ fixedSubcomodule R C M, f m = n) :
    (fixedSubcomodule R C M).toSubmodule.map f.toLinearMap =
      LinearMap.range f.toLinearMap ⊓ (fixedSubcomodule R C N).toSubmodule := by
  ext n
  constructor
  · rintro ⟨m, hm, rfl⟩
    exact ⟨⟨m, rfl⟩, f.mem_fixedSubcomodule hm⟩
  · rintro ⟨hnrange, hn⟩
    exact hLift hn hnrange

/-- Taking invariant vectors commutes with the image of a comodule morphism whose source is
completely reducible, over a commutative ring with a flat coefficient coalgebra. -/
theorem Hom.map_fixedSubcomodule_of_isCompletelyReducible (f : Hom R C M N)
    (hM : IsCompletelyReducible R C M) :
    (fixedSubcomodule R C M).toSubmodule.map f.toLinearMap =
      LinearMap.range f.toLinearMap ⊓ (fixedSubcomodule R C N).toSubmodule :=
  f.map_fixedSubcomodule_of_fixed_preimage (f.exists_fixed_preimage_of_isCompletelyReducible hM)

omit [Module.Flat R C] in
private theorem Hom.fixedMap_surjective_of_fixed_preimage (f : Hom R C M N)
    (hLift : ∀ {n : N}, n ∈ fixedSubcomodule R C N →
      n ∈ LinearMap.range f.toLinearMap → ∃ m ∈ fixedSubcomodule R C M, f m = n)
    (hf : Function.Surjective f) :
    Function.Surjective f.fixedMap := by
  intro n
  obtain ⟨m, hm, hfm⟩ := hLift n.property (hf n)
  exact ⟨⟨m, hm⟩, Subtype.ext (by simpa using hfm)⟩

/-- A surjective comodule morphism with completely reducible source remains surjective on
invariant vectors, over a commutative ring with a flat coefficient coalgebra. -/
theorem Hom.fixedMap_surjective_of_isCompletelyReducible (f : Hom R C M N)
    (hM : IsCompletelyReducible R C M) (hf : Function.Surjective f) :
    Function.Surjective f.fixedMap :=
  f.fixedMap_surjective_of_fixed_preimage (f.exists_fixed_preimage_of_isCompletelyReducible hM) hf

omit [Module.Flat R C] in
private theorem Hom.exact_fixedMap_of_fixed_preimage (f : Hom R C M N) (g : Hom R C N P)
    (hLift : ∀ {n : N}, n ∈ fixedSubcomodule R C N →
      n ∈ LinearMap.range f.toLinearMap → ∃ m ∈ fixedSubcomodule R C M, f m = n)
    (hfg : Function.Exact f g) :
    Function.Exact f.fixedMap g.fixedMap := by
  intro n
  constructor
  · intro hn
    have hgn : g (n : N) = 0 := by simpa using congrArg Subtype.val hn
    obtain ⟨m, hm, hfm⟩ := hLift n.property ((hfg n).mp hgn)
    exact ⟨⟨m, hm⟩, Subtype.ext (by simpa using hfm)⟩
  · rintro ⟨m, rfl⟩
    apply Subtype.ext
    simpa using hfg.apply_apply_eq_zero m

/-- Taking invariants preserves an exact pair of comodule morphisms when the source of the
first morphism is completely reducible and the coefficient coalgebra is flat. -/
theorem Hom.exact_fixedMap_of_isCompletelyReducible (f : Hom R C M N) (g : Hom R C N P)
    (hM : IsCompletelyReducible R C M) (hfg : Function.Exact f g) :
    Function.Exact f.fixedMap g.fixedMap :=
  f.exact_fixedMap_of_fixed_preimage g (f.exists_fixed_preimage_of_isCompletelyReducible hM) hfg

end Ring

section Field

variable {k : Type u} [Field k]
variable {C : Type v} [AddCommMonoid C] [Module k C] [Coalgebra k C] [One C]
variable {M : Type w} [AddCommMonoid M] [Module k M] [Comodule k C M]
variable {N : Type x} [AddCommMonoid N] [Module k N] [Comodule k C N]
variable {P : Type y} [AddCommMonoid P] [Module k P] [Comodule k C P]

/-- In a comodule over a linearly reductive coalgebra, every invariant vector in the image of
any comodule morphism has an invariant preimage, with no finiteness assumptions on the modules. -/
theorem Hom.exists_fixed_preimage_of_isLinearlyReductive (f : Hom k C M N)
    (hC : Coalgebra.IsLinearlyReductive.{u, v, u} k C) {n : N}
    (hn : n ∈ fixedSubcomodule k C N) (hnrange : n ∈ LinearMap.range f.toLinearMap) :
    ∃ m ∈ fixedSubcomodule k C M, f m = n := by
  let : AddCommGroup C := Module.addCommMonoidToAddCommGroup k
  let : Module.Free k C := Module.Free.of_divisionRing k C
  obtain ⟨m, hm⟩ := hnrange
  obtain ⟨S, hS, hmS⟩ := Subcomodule.exists_finite_subcomodule_mem (R := k) (C := C) m
  let : Module.Finite k S := hS
  obtain ⟨s, hs, hfs⟩ := (f.comp S.subtype).exists_fixed_preimage_of_isCompletelyReducible
    hC.isCompletelyReducible hn ⟨⟨m, hmS⟩, by simpa using hm⟩
  exact ⟨s, by simpa using S.subtype.mem_fixedSubcomodule hs, by simpa using hfs⟩

/-- Taking invariant vectors commutes with the image of any comodule morphism over a linearly
reductive coalgebra. -/
theorem Hom.map_fixedSubcomodule_of_isLinearlyReductive (f : Hom k C M N)
    (hC : Coalgebra.IsLinearlyReductive.{u, v, u} k C) :
    (fixedSubcomodule k C M).toSubmodule.map f.toLinearMap =
      LinearMap.range f.toLinearMap ⊓ (fixedSubcomodule k C N).toSubmodule :=
  f.map_fixedSubcomodule_of_fixed_preimage (f.exists_fixed_preimage_of_isLinearlyReductive hC)

/-- A surjective comodule morphism over a linearly reductive coalgebra remains surjective on
invariant vectors, even for infinite-dimensional comodules. -/
theorem Hom.fixedMap_surjective_of_isLinearlyReductive (f : Hom k C M N)
    (hC : Coalgebra.IsLinearlyReductive.{u, v, u} k C) (hf : Function.Surjective f) :
    Function.Surjective f.fixedMap :=
  f.fixedMap_surjective_of_fixed_preimage (f.exists_fixed_preimage_of_isLinearlyReductive hC) hf

/-- Taking invariants preserves exact pairs of comodule morphisms over a linearly reductive
coalgebra. Combined with injectivity and surjectivity of the restricted maps, this preserves
short exact sequences of arbitrary rational representations. -/
theorem Hom.exact_fixedMap_of_isLinearlyReductive (f : Hom k C M N) (g : Hom k C N P)
    (hC : Coalgebra.IsLinearlyReductive.{u, v, u} k C) (hfg : Function.Exact f g) :
    Function.Exact f.fixedMap g.fixedMap :=
  f.exact_fixedMap_of_fixed_preimage g (f.exists_fixed_preimage_of_isLinearlyReductive hC) hfg

end Field

end TauCeti.Comodule
