/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Scheme.LocalDimension
public import TauCeti.Topology.PureDimension
import TauCeti.AlgebraicGeometry.Scheme.StalkSpecializes
import TauCeti.Topology.Sober

/-!
# Points and local rings of pure-dimensional schemes over a field

Let `X` be a scheme locally of finite type over a field `k` and pure of dimension `d`: every
irreducible component of `X` has dimension `d`. Since the closure of a point `x` has dimension
`trdeg_k κ(x)`, the transcendence degrees of the residue fields of `X` are at most `d`, and they
reach `d` exactly at the generic points of the irreducible components. A point `η` with
`trdeg_k κ(η) ≥ d` therefore has no proper generization.

Read in a local ring `𝒪_{X,x}`, whose primes are the generizations of `x`, this says that a prime
`P` of `𝒪_{X,x}` whose residue field has transcendence degree at least `d` over `k` is a minimal
prime. At a closed point `x`, whose closure is a point, `dim_x X = dim 𝒪_{X,x} + dim {x}⁻` gives
`dim 𝒪_{X,x} = d`.

These are the two dimension inputs to the proof that a reduced scheme of pure dimension `d` over a
field of characteristic zero whose differentials have a locally free quotient of rank `d` is
smooth: at a closed point, the local algebra argument shows the quotient is an isomorphism when
every prime with residue field of transcendence degree at least `d` is minimal, and the local ring
is then regular as soon as its dimension is at least `d`.

## Main results

All in the namespace `TauCeti.AlgebraicGeometry`:

* `trdeg_residueField_le_of_isPureDimensional`: `trdeg_k κ(x) ≤ d` at every point.
* `mem_genericPoints_iff_trdeg_residueField_eq`: the generic points of the irreducible components
  are the points with `trdeg_k κ(x) = d`.
* `mem_minimalPrimes_stalk_of_le_trdeg`: a prime of `𝒪_{X,x}` whose residue field has
  transcendence degree at least `d` over `k` is a minimal prime.
* `ringKrullDim_stalk_eq_of_isPureDimensional`: at a closed point `x`, `dim 𝒪_{X,x} = d`.

## References

* A. Nobile, *Notes on Nash modification*, arXiv:2404.09102, Section 2, proof of Proposition 2.3
  (the dimension count at a minimal prime over the annihilator of the differentials).
* [Stacks Project, Tag 00P0](https://stacks.math.columbia.edu/tag/00P0) (dimension of finite type
  algebras over a field).
-/

public section

open CategoryTheory AlgebraicGeometry Topology IsLocalRing

namespace TauCeti.AlgebraicGeometry

universe u

section ResidueFieldComap

variable {k : Type u} [CommRing k] {X : Scheme.{u}} [X.Over (Spec (.of k))]

/-- For a generization `η ⤳ x`, the residue field of the prime of `𝒪_{X,x}` lying under the
maximal ideal of `𝒪_{X,η}` embeds into `κ(η)` over `k`, so its transcendence degree is at most
that of `κ(η)`. -/
private theorem trdeg_residueField_comap_le {x η : X} (hηx : η ⤳ x)
    (P : Ideal (X.presheaf.stalk x)) [P.IsPrime]
    (hP : (maximalIdeal (X.presheaf.stalk η)).comap (X.presheaf.stalkSpecializes hηx).hom = P) :
    Algebra.trdeg k P.ResidueField ≤ Algebra.trdeg k (X.residueField η) := by
  -- The specialization map followed by the residue map is a `k`-algebra map `𝒪_{X,x} → κ(η)`.
  have hcomm : X.presheaf.germ ⊤ x trivial ≫ X.presheaf.stalkSpecializes hηx ≫ X.residue η =
      X.presheaf.germ ⊤ η trivial ≫ X.residue η :=
    X.presheaf.germ_stalkSpecializes_assoc trivial hηx (X.residue η)
  let f : X.presheaf.stalk x →ₐ[k] X.residueField η :=
    { toRingHom := (X.presheaf.stalkSpecializes hηx ≫ X.residue η).hom
      commutes' c := by
        simp only [Scheme.algebraMap_stalk_eq_baseRingToStalk, Scheme.baseRingToStalk_apply,
          Scheme.algebraMap_residueField_eq_residue_comp_baseRingToStalk, RingHom.comp_apply]
        exact congr($hcomm (Scheme.Modules.baseRingToGlobalSections k X c)) }
  have hker (a : X.presheaf.stalk x) : f a = 0 ↔ a ∈ P := by
    -- `f a` is by definition the residue of the image of `a` in `𝒪_{X,η}`.
    rw [← hP, Ideal.mem_comap, ← residue_eq_zero_iff]
    rfl
  let g := Ideal.ResidueField.liftₐ P f (fun a ha ↦ (hker a).mpr ha)
    (fun a ha ↦ (isUnit_iff_ne_zero.mpr fun h0 ↦ ha ((hker a).mp h0)))
  exact trdeg_le_of_injective g g.toRingHom.injective

end ResidueFieldComap

variable (k : Type u) [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
  [LocallyOfFiniteType (X ↘ Spec (.of k))] {d : ℕ}

/-- On a scheme locally of finite type over `k` and pure of dimension `d`, the residue field at the
generic point of an irreducible component has transcendence degree `d` over `k`. -/
private theorem trdeg_residueField_eq_of_mem_genericPoints (h : IsPureDimensional d X) {x : X}
    (hx : x ∈ genericPoints X) : Algebra.trdeg k (X.residueField x) = d := by
  have hdim := topologicalKrullDim_closure_singleton_eq_toNat_trdeg_residueField k x
  rw [isPureDimensional_iff.mp h _ hx] at hdim
  have hd : d = (Algebra.trdeg k (X.residueField x)).toNat := by exact_mod_cast hdim
  rw [hd, Cardinal.cast_toNat_of_lt_aleph0 (trdeg_residueField_lt_aleph0 k x)]

include k in
/-- Every point `x` has a generization `ξ ⤳ x` that is the generic point of an irreducible
component, and the closure of `ξ` has dimension `d`. -/
private theorem exists_le_mem_genericPoints (h : IsPureDimensional d X) (x : X) :
    ∃ ξ ∈ genericPoints X, x ≤ ξ ∧ Order.height ξ = d := by
  obtain ⟨ξ, -, hξx, hmax⟩ := isClosed_univ.exists_maximal_specializes (Set.mem_univ x)
  have hξ : ξ ∈ genericPoints X :=
    TauCeti.mem_genericPoints_iff.mpr fun y hy ↦ hmax y (Set.mem_univ y) hy
  refine ⟨ξ, hξ, hξx, ?_⟩
  rw [height_eq_toNat_trdeg_residueField k, trdeg_residueField_eq_of_mem_genericPoints k h hξ,
    Cardinal.toNat_natCast]

/-- **Transcendence degrees of residue fields on a pure-dimensional scheme.** On a scheme locally
of finite type over a field `k` and pure of dimension `d`, every residue field has transcendence
degree at most `d` over `k`. -/
theorem trdeg_residueField_le_of_isPureDimensional (h : IsPureDimensional d X) (x : X) :
    Algebra.trdeg k (X.residueField x) ≤ d := by
  obtain ⟨ξ, -, hxξ, hξ⟩ := exists_le_mem_genericPoints k h x
  have hle := Order.height_mono hxξ
  rw [hξ, height_eq_toNat_trdeg_residueField k] at hle
  rw [← Cardinal.cast_toNat_of_lt_aleph0 (trdeg_residueField_lt_aleph0 k x)]
  exact_mod_cast hle

/-- **Generic points of a pure-dimensional scheme.** On a scheme locally of finite type over a
field `k` and pure of dimension `d`, a point is the generic point of an irreducible component if
and only if its residue field has transcendence degree `d` over `k`. -/
theorem mem_genericPoints_iff_trdeg_residueField_eq (h : IsPureDimensional d X) (x : X) :
    x ∈ genericPoints X ↔ Algebra.trdeg k (X.residueField x) = d := by
  refine ⟨trdeg_residueField_eq_of_mem_genericPoints k h, fun hx ↦ ?_⟩
  obtain ⟨ξ, hξ, hxξ, hξd⟩ := exists_le_mem_genericPoints k h x
  have hxd : Order.height x = d := by
    rw [height_eq_toNat_trdeg_residueField k, hx, Cardinal.toNat_natCast]
  -- A proper generization `ξ` of `x` would have larger height, but both heights are `d`.
  have hξx : ξ ≤ x := by
    by_contra hξx
    have hlt := Order.height_strictMono (lt_of_le_not_ge hxξ hξx)
      (hxd.trans_lt (ENat.natCast_lt_top d))
    rw [hxd, hξd] at hlt
    exact lt_irrefl _ hlt
  rwa [(Specializes.antisymm hξx hxξ).eq]

/-- **Minimal primes of a local ring of a pure-dimensional scheme.** Let `X` be a scheme locally of
finite type over a field `k` and pure of dimension `d`, and let `x ∈ X`. A prime `P` of the local
ring `𝒪_{X,x}` whose residue field has transcendence degree at least `d` over `k` is a minimal
prime of `𝒪_{X,x}`. -/
theorem mem_minimalPrimes_stalk_of_le_trdeg (h : IsPureDimensional d X) (x : X)
    (P : Ideal (X.presheaf.stalk x)) [P.IsPrime]
    (hP : (d : Cardinal) ≤ Algebra.trdeg k P.ResidueField) :
    P ∈ minimalPrimes (X.presheaf.stalk x) := by
  -- `P` is the prime of a generization `η` of `x`, of codimension the height of `P`.
  obtain ⟨η, hcoh, hηx, hηP⟩ :=
    Scheme.exists_specializes_and_comap_stalkSpecializes_maximalIdeal_eq P
  have hη : η ∈ genericPoints X :=
    (mem_genericPoints_iff_trdeg_residueField_eq k h η).mpr <|
      (trdeg_residueField_le_of_isPureDimensional k h η).antisymm
        (hP.trans (trdeg_residueField_comap_le hηx P hηP))
  rw [← Ideal.height_eq_zero_iff, ← hcoh, Order.coheight_eq_zero]
  exact fun y hy ↦ (TauCeti.mem_genericPoints_iff.mp hη y hy).le

include k in
/-- **Local rings at closed points of a pure-dimensional scheme.** On a scheme locally of finite
type over a field and pure of dimension `d`, the local ring at a closed point has dimension `d`. -/
theorem ringKrullDim_stalk_eq_of_isPureDimensional (h : IsPureDimensional d X) {x : X}
    (hx : IsClosed {x}) : ringKrullDim (X.presheaf.stalk x) = d := by
  -- A closed point has no proper specialization, so its closure has dimension zero.
  have hmin : IsMin x := fun y (hy : x ⤳ y) ↦ (Set.mem_singleton_iff.mp (hy.mem_closed hx rfl)).ge
  have hdim := topologicalKrullDimAt_eq_ringKrullDim_stalk_add_topologicalKrullDim_closure k x
  rw [topologicalKrullDimAt_eq_of_isPureDimensional k h x,
    ← height_eq_topologicalKrullDim_closure_singleton, Order.height_eq_zero.mpr hmin] at hdim
  simpa using hdim.symm

end TauCeti.AlgebraicGeometry
