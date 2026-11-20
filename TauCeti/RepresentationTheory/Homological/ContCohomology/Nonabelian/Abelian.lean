/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.ExplicitFunctoriality
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Nonabelian.Basic
public import TauCeti.Topology.Algebra.ContinuousMonoidHom.TypeTags
public import TauCeti.Topology.Algebra.GroupAction.TypeTags

/-!
# Nonabelian first cohomology with commutative coefficients

Let a group `G` with a topology act continuously on a commutative topological group `M`, written
additively. Then `G` acts by automorphisms on `Multiplicative M`
(`Multiplicative.mulDistribMulAction`), and the continuous nonabelian cohomology
`H¹(G, Multiplicative M)` of
`TauCeti.RepresentationTheory.Homological.ContCohomology.Nonabelian.Basic` is defined. This file
shows that it is the explicit continuous cohomology group `TauCeti.ContCohomology.H1 G M`, so that
the nonabelian theory specializes to the abelian one rather than being a second abelian cohomology
theory beside it.

Read additively, the ordered cocycle identity `f (g * h) = f g * g • f h` is the identity
`f (g * h) = f g + g • f h`, which is `groupCohomology.IsCocycle₁ f`; so the nonabelian cocycles
with values in `Multiplicative M` are the explicit continuous cocycles `ContCohomology.Z1 G M`, by
the identity on underlying functions. The twist of a cocycle `f` by `a`,
`g ↦ a⁻¹ * f g * g • a`, is the translate `f + d⁰ a` of `f` by the coboundary
`(d⁰ a) g = g • a - a`, so the cohomology relation is congruence modulo `B¹`, and the two quotients
agree. On the zeroth level, the invariants `FixedPoints.subgroup G (Multiplicative M)` are the
additive invariants `ContCohomology.H0 G M` (`FixedPoints.subgroup_multiplicative`).

The comparison is natural: it intertwines the map induced by a compatible pair on nonabelian `H¹`
with the explicit pullback `ContCohomology.explicitMap1`. For a general commutative coefficient
group `A`, the ordered cocycle identity is Mathlib's commutative `groupCohomology.IsMulCocycle₁`,
the order of the two factors being immaterial.

## Main definitions

* `TauCeti.NonabelianH1.Cocycle.multiplicativeEquivZ1`: the nonabelian cocycles with values in
  `Multiplicative M` are the explicit continuous cocycles `ContCohomology.Z1 G M`.
* `TauCeti.NonabelianH1.multiplicativeEquivH1`: the bijection of pointed sets
  `H¹(G, Multiplicative M) ≃ ContCohomology.H1 G M`.
* `TauCeti.NonabelianH1.Cocycle.ofIsMulCocycle₁`: the cocycle given by a continuous map satisfying
  `groupCohomology.IsMulCocycle₁`, for commutative coefficients.

## Main results

* `TauCeti.NonabelianH1.Cocycle.coe_multiplicativeEquivZ1_twist`: twisting a cocycle by `a` adds
  the coboundary `d⁰ a`.
* `TauCeti.NonabelianH1.multiplicativeEquivH1_mk` and
  `TauCeti.NonabelianH1.multiplicativeEquivH1_one`: the bijection is compatible with the class maps
  and sends the base point to `0`.
* `TauCeti.NonabelianH1.multiplicativeEquivH1_map`: naturality in compatible pairs.
* `TauCeti.NonabelianH1.Cocycle.isMulCocycle₁`: for commutative coefficients a cocycle satisfies
  `groupCohomology.IsMulCocycle₁`.

## References

* J.-P. Serre, *Galois Cohomology*, Springer, 1997, I.5.1.
* M. Kim, *The motivic fundamental group of `P¹ ∖ {0, 1, ∞}` and the theorem of Siegel*,
  Invent. Math. 161 (2005), §1.
-/

public section

open Multiplicative (ofAdd toAdd)

namespace TauCeti

namespace NonabelianH1

section CommGroup

variable {G A : Type*} [Group G] [TopologicalSpace G] [CommGroup A] [TopologicalSpace A]
  [MulDistribMulAction G A]

/-- For commutative coefficients a cocycle satisfies Mathlib's `groupCohomology.IsMulCocycle₁`,
`f (g * h) = g • f h * f g`: the ordered cocycle identity with its two factors exchanged. -/
theorem Cocycle.isMulCocycle₁ (f : Cocycle G A) : groupCohomology.IsMulCocycle₁ f :=
  fun g h ↦ by rw [f.apply_mul, mul_comm]

/-- For commutative coefficients, the cocycle given by a continuous map satisfying Mathlib's
`groupCohomology.IsMulCocycle₁`. -/
def Cocycle.ofIsMulCocycle₁ (f : G → A) (hf : Continuous f)
    (hcocycle : groupCohomology.IsMulCocycle₁ f) : Cocycle G A where
  toFun := f
  continuous_toFun := hf
  map_mul' g h := by rw [hcocycle, mul_comm]

@[simp]
theorem Cocycle.coe_ofIsMulCocycle₁ (f : G → A) (hf : Continuous f)
    (hcocycle : groupCohomology.IsMulCocycle₁ f) : ⇑(Cocycle.ofIsMulCocycle₁ f hf hcocycle) = f :=
  (rfl)

end CommGroup

variable {G M : Type*} [Group G] [TopologicalSpace G] [AddCommGroup M] [TopologicalSpace M]
  [IsTopologicalAddGroup M] [DistribMulAction G M]

namespace Cocycle

/-- A nonabelian cocycle with values in `Multiplicative M`, read additively, is an explicit
continuous cocycle. -/
private theorem toAdd_comp_mem_Z1 (f : Cocycle G (Multiplicative M)) :
    (fun g ↦ toAdd (f g)) ∈ ContCohomology.Z1 G M :=
  ContCohomology.mem_Z1_iff.2 ⟨continuous_toAdd.comp f.continuous, fun g h ↦ by
    beta_reduce
    rw [f.apply_mul, toAdd_mul, Multiplicative.toAdd_smul, add_comm]⟩

/-- The nonabelian cocycles with values in `Multiplicative M` are the explicit continuous cocycles
`ContCohomology.Z1 G M`, by the identity on underlying functions. -/
def multiplicativeEquivZ1 : Cocycle G (Multiplicative M) ≃ ContCohomology.Z1 G M where
  toFun f := ⟨fun g ↦ toAdd (f g), toAdd_comp_mem_Z1 f⟩
  invFun c :=
    { toFun g := ofAdd ((c : G → M) g)
      continuous_toFun := continuous_ofAdd.comp (ContCohomology.mem_Z1_iff.1 c.2).1
      map_mul' g h := by
        rw [(ContCohomology.mem_Z1_iff.1 c.2).2 g h, ← Multiplicative.ofAdd_smul, ← ofAdd_add,
          add_comm] }
  left_inv _ := ext fun _ ↦ rfl
  right_inv _ := Subtype.ext rfl

@[simp]
theorem coe_multiplicativeEquivZ1_apply (f : Cocycle G (Multiplicative M)) (g : G) :
    (multiplicativeEquivZ1 f : G → M) g = toAdd (f g) :=
  (rfl)

@[simp]
theorem multiplicativeEquivZ1_symm_apply (c : ContCohomology.Z1 G M) (g : G) :
    multiplicativeEquivZ1.symm c g = ofAdd ((c : G → M) g) :=
  (rfl)

/-- The trivial cocycle corresponds to the zero cocycle. -/
@[simp]
theorem multiplicativeEquivZ1_one :
    multiplicativeEquivZ1 (1 : Cocycle G (Multiplicative M)) = 0 :=
  Subtype.ext (funext fun _ ↦ toAdd_one)

/-- Twisting a cocycle by `a` adds the coboundary `d⁰ a`: read additively, the twist
`g ↦ a⁻¹ * f g * g • a` is `g ↦ f g + (g • a - a)`. -/
@[simp]
theorem coe_multiplicativeEquivZ1_twist [ContinuousSMul G M] (f : Cocycle G (Multiplicative M))
    (a : Multiplicative M) :
    (multiplicativeEquivZ1 (f.twist a) : G → M) =
      multiplicativeEquivZ1 f + ContCohomology.d0 G M (toAdd a) := by
  ext g
  simp only [coe_multiplicativeEquivZ1_apply, twist_apply, toAdd_mul, toAdd_inv,
    Multiplicative.toAdd_smul, Pi.add_apply, ContCohomology.d0_apply]
  abel

/-- Two nonabelian cocycles with values in `Multiplicative M` are cohomologous exactly when the
corresponding explicit cocycles differ by a coboundary. -/
theorem equiv_iff_sub_mem_B1 {f f' : Cocycle G (Multiplicative M)} :
    f ≈ f' ↔
      (multiplicativeEquivZ1 f' : G → M) - multiplicativeEquivZ1 f ∈ ContCohomology.B1 G M := by
  rw [equiv_iff, ContCohomology.mem_B1_iff]
  refine ⟨fun ⟨a, ha⟩ ↦ ⟨toAdd a, fun g ↦ ?_⟩, fun ⟨m, hm⟩ ↦ ⟨ofAdd m, fun g ↦ ?_⟩⟩
  · simp only [Pi.sub_apply, coe_multiplicativeEquivZ1_apply, ha, toAdd_mul, toAdd_inv,
      Multiplicative.toAdd_smul]
    abel
  · apply toAdd.injective
    have hg : toAdd (f' g) = toAdd (f g) + (g • m - m) := by
      rw [hm g, Pi.sub_apply, coe_multiplicativeEquivZ1_apply, coe_multiplicativeEquivZ1_apply,
        add_sub_cancel]
    simp only [toAdd_mul, toAdd_inv, Multiplicative.toAdd_smul, toAdd_ofAdd, hg]
    abel

end Cocycle

/-- Two nonabelian cocycles with values in `Multiplicative M` have the same class exactly when the
corresponding explicit cocycles differ by a coboundary. -/
private theorem mk_eq_mk_iff_sub_mem_B1 {f f' : Cocycle G (Multiplicative M)} :
    mk f = mk f' ↔
      (Cocycle.multiplicativeEquivZ1 f : G → M) - Cocycle.multiplicativeEquivZ1 f' ∈
        ContCohomology.B1 G M := by
  rw [mk_eq_mk_iff, ← Cocycle.equiv_iff, Cocycle.equiv_iff_sub_mem_B1, ← neg_mem_iff, neg_sub]

variable [ContinuousSMul G M]

/-- The class in `H¹(G, Multiplicative M)` of an explicit continuous cocycle class, the inverse of
`TauCeti.NonabelianH1.multiplicativeEquivH1`. -/
private def ofH1 (x : ContCohomology.H1 G M) : NonabelianH1 G (Multiplicative M) :=
  Quotient.liftOn' x (fun c ↦ mk (Cocycle.multiplicativeEquivZ1.symm c)) fun c c' h ↦
    mk_eq_mk_iff_sub_mem_B1.2 <| by
      simpa only [Equiv.apply_symm_apply] using ContCohomology.H1pi_eq_iff.1 (Quotient.sound h)

private theorem ofH1_mk (f : Cocycle G (Multiplicative M)) :
    ofH1 (Cocycle.multiplicativeEquivZ1 f : ContCohomology.H1 G M) = mk f := by
  rw [ofH1, QuotientAddGroup.quotient_liftOn_mk, Equiv.symm_apply_apply]

private theorem ofH1_bijective : Function.Bijective (ofH1 (G := G) (M := M)) := by
  refine ⟨fun x x' h ↦ ?_, fun c ↦ ?_⟩
  · obtain ⟨f, rfl⟩ := (QuotientAddGroup.mk_surjective.comp
      Cocycle.multiplicativeEquivZ1.surjective) x
    obtain ⟨f', rfl⟩ := (QuotientAddGroup.mk_surjective.comp
      Cocycle.multiplicativeEquivZ1.surjective) x'
    exact ContCohomology.H1pi_eq_iff.2 <| mk_eq_mk_iff_sub_mem_B1.1 <| by
      simpa only [Function.comp_apply, ofH1_mk] using h
  · induction c using induction_on with | mk f =>
    exact ⟨_, ofH1_mk f⟩

/-- **Nonabelian `H¹` with commutative coefficients is the explicit abelian `H¹`**: the bijection
`H¹(G, Multiplicative M) ≃ ContCohomology.H1 G M` induced by
`TauCeti.NonabelianH1.Cocycle.multiplicativeEquivZ1`. It sends the base point to `0`
(`TauCeti.NonabelianH1.multiplicativeEquivH1_one`). -/
noncomputable def multiplicativeEquivH1 :
    NonabelianH1 G (Multiplicative M) ≃ ContCohomology.H1 G M :=
  (Equiv.ofBijective _ ofH1_bijective).symm

/-- The comparison sends the class of a cocycle to the class of the corresponding explicit
cocycle. -/
@[simp]
theorem multiplicativeEquivH1_mk (f : Cocycle G (Multiplicative M)) :
    multiplicativeEquivH1 (mk f) = (Cocycle.multiplicativeEquivZ1 f : ContCohomology.H1 G M) :=
  (Equiv.ofBijective _ ofH1_bijective).symm_apply_eq.2 (ofH1_mk f).symm

@[simp]
theorem multiplicativeEquivH1_symm_mk (c : ContCohomology.Z1 G M) :
    multiplicativeEquivH1.symm (c : ContCohomology.H1 G M) =
      mk (Cocycle.multiplicativeEquivZ1.symm c) :=
  multiplicativeEquivH1.symm_apply_eq.2 <| by
    rw [multiplicativeEquivH1_mk, Equiv.apply_symm_apply]

/-- The comparison sends the base point to `0`. -/
@[simp]
theorem multiplicativeEquivH1_one :
    multiplicativeEquivH1 (1 : NonabelianH1 G (Multiplicative M)) = 0 := by
  rw [one_def, multiplicativeEquivH1_mk, Cocycle.multiplicativeEquivZ1_one,
    QuotientAddGroup.mk_zero]

/-- A class is the base point exactly when its image in the explicit abelian `H¹` is `0`. -/
@[simp]
theorem multiplicativeEquivH1_eq_zero_iff {c : NonabelianH1 G (Multiplicative M)} :
    multiplicativeEquivH1 c = 0 ↔ c = 1 := by
  rw [← multiplicativeEquivH1_one, multiplicativeEquivH1.apply_eq_iff_eq]

@[simp]
theorem multiplicativeEquivH1_symm_zero :
    multiplicativeEquivH1.symm (0 : ContCohomology.H1 G M) = 1 :=
  multiplicativeEquivH1.symm_apply_eq.2 multiplicativeEquivH1_one.symm

section Map

variable {G' N : Type*} [Group G'] [TopologicalSpace G'] [AddCommGroup N] [TopologicalSpace N]
  [IsTopologicalAddGroup N] [DistribMulAction G' N] [ContinuousSMul G' N]

/-- **Naturality of the comparison**: it intertwines the map induced by a compatible pair on
nonabelian `H¹` with the explicit pullback `ContCohomology.explicitMap1` on abelian `H¹`. -/
theorem multiplicativeEquivH1_map (ψ : G' →ₜ* G) (φ : M →ₜ+ N)
    (h : ∀ (g : G') (m : M), φ (ψ g • m) = g • φ m) (c : NonabelianH1 G (Multiplicative M)) :
    multiplicativeEquivH1 (map ψ φ.toMultiplicative (φ.toMultiplicative_map_smul ψ h) c) =
      ContCohomology.explicitMap1 G M G' N ψ φ φ.continuous h (multiplicativeEquivH1 c) := by
  induction c using induction_on with | mk f =>
  rw [map_mk, multiplicativeEquivH1_mk, multiplicativeEquivH1_mk,
    ContCohomology.explicitMap1_mk]
  congr 1
  ext g
  simp [ContCohomology.cocyclesMap1_apply]

end Map

end NonabelianH1

end TauCeti
