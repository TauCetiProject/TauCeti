/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.IntegralLattice.Norm
public import TauCeti.NumberTheory.IntegralLattice.Localization.Basic
public import TauCeti.NumberTheory.QuadraticForm.OrthogonalGroup.Integral.CompactOpen
import TauCeti.LinearAlgebra.Basis.RangeSpan
import TauCeti.Logic.Equiv.Set
import TauCeti.NumberTheory.Padics.RatCast

/-!
# The local stabilizers of an integral lattice

Let `L` be an integral lattice in a rational vector space `V`, with norm form `Q(x) = B(x, x)`.
At a prime `p`, the completed rational space `V_p = ℚ_p ⊗[ℚ] V` contains the image of the integral
localization `L_p = ℤ_p ⊗[ℤ] L` under the canonical injection
`TauCeti.IntegralLattice.localizationToCompletion`. The **local stabilizer** of `L` at `p` is

```text
K_p(L) = {g ∈ O(V_p) : g L_p = L_p},
```

the isometries of the completed space which, together with their inverses, map the image of
`L_p` into itself. Its intersection with `SO(V_p)` is the proper local stabilizer `K_p⁺(L)`.
These are the compact open subgroups that cut the adelic orthogonal group down to the class set
of the genus of `L`.

In a `ℤ`-basis `e` of `L`, which is also a `ℚ`-basis of `V`, the image of `L_p` consists of the
vectors whose coordinates are `p`-adic integers. So `K_p(L)` is the subgroup of isometries whose
matrices in `e`, and those of their inverses, have entries in `ℤ_p`
(`TauCeti.IntegralLattice.localStabilizer_eq_integralOrthogonalSubgroup`). This identifies it with
the integral orthogonal subgroup of `e`, which makes it compact and open, and shows that it agrees
with the integral orthogonal subgroup of any fixed rational basis at almost every prime.

A rational isometry `g` of `V` lies in `K_p(L)` at every prime exactly when it preserves `L`
(`TauCeti.IntegralLattice.forall_orthogonalGroupBaseChange_mem_localStabilizer_iff`). Indeed both
conditions say that the matrices of `g` and `g⁻¹` in `e` have integral entries, and a rational
number is an integer exactly when it is a `p`-adic integer at every prime. So the rational
isometries lying in `∏_p K_p(L)` are exactly the isometries of `L`: this is the stabilizer of the
base point in the dictionary between the classes in the genus of `L` and the finite adelic double
cosets `O(V)(ℚ) \ O(V)(𝔸_f) / ∏_p K_p(L)`.

For a nondegenerate lattice, the local stabilizers are the orthogonal reference subgroups of a
compatible compact-open tuple `TauCeti.IntegralLattice.orthogonalCompactOpens`. Its finite adelic
double cosets are the class sets `O(V)(ℚ) \ O(V)(𝔸_f) / ∏_p K_p(L)` and
`SO(V)(ℚ) \ SO(V)(𝔸_f) / ∏_p K_p⁺(L)` on which the adelic description of the genus is stated; the
comparison of these double cosets with the classes in the genus is not done here.

## Main definitions

* `TauCeti.IntegralLattice.localStabilizer`: the local stabilizer `K_p(L)`.
* `TauCeti.IntegralLattice.orthogonalCompactOpens`: for a nondegenerate lattice, the compatible
  compact-open tuple whose orthogonal reference subgroups are the local stabilizers.

## Main results

* `TauCeti.IntegralLattice.mem_localStabilizer_iff`: `g ∈ K_p(L)` exactly when `g` maps the image
  of `L_p` onto itself.
* `TauCeti.IntegralLattice.localStabilizer_eq_integralOrthogonalSubgroup`: in any basis of `L`,
  the local stabilizer is the integral orthogonal subgroup.
* `TauCeti.IntegralLattice.isOpen_localStabilizer`,
  `TauCeti.IntegralLattice.isCompact_localStabilizer`: `K_p(L)` is compact and open.
* `TauCeti.IntegralLattice.eventually_localStabilizer_eq`: for a fixed rational basis of `V`,
  `K_p(L)` is its integral orthogonal subgroup at almost every prime.
* `TauCeti.IntegralLattice.forall_orthogonalGroupBaseChange_mem_localStabilizer_iff`: a rational
  isometry lies in every local stabilizer exactly when it preserves `L`.

## References

* O. T. O'Meara, *Introduction to Quadratic Forms* (1963), §§101–102, for the stabilizers of a
  lattice in the local orthogonal groups and the adelic description of the genus.
* M. Kneser, *Quadratische Formen* (2002), §§21–22.
-/

public section

open Module Filter TauCeti.QuadraticMap
open scoped TensorProduct

namespace TauCeti

namespace IntegralLattice

variable {V : Type*} [AddCommGroup V] [Module ℚ V] (L : IntegralLattice V)

section Stabilizer

variable (p : ℕ) [Fact p.Prime]

/-- **The local stabilizer** `K_p(L)` of an integral lattice at a prime `p`: the isometries of the
completed rational space `V_p` which map the image of the integral localization `L_p` onto
itself. -/
def localStabilizer : Subgroup (orthogonalGroup (L.norm.baseChange ℚ_[p])) where
  carrier := {g | ∀ x, (g : ℚ_[p] ⊗[ℚ] V ≃ₗ[ℚ_[p]] ℚ_[p] ⊗[ℚ] V) x ∈
    LinearMap.range (L.localizationToCompletion p) ↔
      x ∈ LinearMap.range (L.localizationToCompletion p)}
  one_mem' _ := Iff.rfl
  mul_mem' {g h} hg hh x := (hg _).trans (hh x)
  inv_mem' {g} hg x := by
    rw [← hg]
    simp

variable {L p} in
/-- An isometry of `V_p` lies in `K_p(L)` exactly when it maps the image of `L_p` onto itself. -/
@[simp]
theorem mem_localStabilizer_iff {g : orthogonalGroup (L.norm.baseChange ℚ_[p])} :
    g ∈ L.localStabilizer p ↔ ∀ x, (g : ℚ_[p] ⊗[ℚ] V ≃ₗ[ℚ_[p]] ℚ_[p] ⊗[ℚ] V) x ∈
      LinearMap.range (L.localizationToCompletion p) ↔
        x ∈ LinearMap.range (L.localizationToCompletion p) :=
  Iff.rfl

/-- **The local stabilizer is an integral orthogonal subgroup.** In the rational basis of any basis
`e` of `L`, the local stabilizer `K_p(L)` consists of the isometries whose matrices, and those of
their inverses, have `p`-adic integral entries. -/
theorem localStabilizer_eq_integralOrthogonalSubgroup {ι : Type*} [Fintype ι] [DecidableEq ι]
    (e : Basis ι ℤ L) :
    L.localStabilizer p =
      integralOrthogonalSubgroup (L.norm.baseChange ℚ_[p])
        ((e.extendOfIsLattice ℚ).baseChange ℚ_[p]) := by
  have hspan : (Submodule.span (PadicInt.subring p)
      (Set.range ((e.extendOfIsLattice ℚ).baseChange ℚ_[p])) : Set (ℚ_[p] ⊗[ℚ] V)) =
        LinearMap.range (L.localizationToCompletion p) := Set.ext fun x ↦ by
    rw [SetLike.mem_coe, SetLike.mem_coe, Basis.mem_span_iff_repr_mem,
      L.mem_range_localizationToCompletion_iff p e]
    exact forall_congr' fun i ↦ ⟨fun ⟨a, ha⟩ ↦ ha ▸ a.2, fun h ↦ ⟨⟨_, h⟩, rfl⟩⟩
  ext g
  rw [mem_localStabilizer_iff, mem_integralOrthogonalSubgroup_iff_mem_span]
  refine (Equiv.forall_apply_mem_iff_iff_mapsTo (g : ℚ_[p] ⊗[ℚ] V ≃ₗ[ℚ_[p]] ℚ_[p] ⊗[ℚ] V).toEquiv
    _ (LinearMap.range (L.localizationToCompletion p) : Set (ℚ_[p] ⊗[ℚ] V))).trans ?_
  rw [← hspan]
  simp only [Set.MapsTo, LinearEquiv.coe_toEquiv, LinearEquiv.coe_toEquiv_symm, EquivLike.coe_coe,
    SetLike.mem_coe, Subgroup.coe_inv, LinearEquiv.coe_inv]
  -- The two sides now differ only in binder annotations.
  exact Iff.rfl

/-- The local stabilizer of `L` is open in the local orthogonal group. -/
theorem isOpen_localStabilizer :
    IsOpen (L.localStabilizer p : Set (orthogonalGroup (L.norm.baseChange ℚ_[p]))) := by
  classical
  rw [L.localStabilizer_eq_integralOrthogonalSubgroup p (Free.chooseBasis ℤ L)]
  exact isOpen_integralOrthogonalSubgroup _ _

/-- The local stabilizer of `L` is compact. -/
theorem isCompact_localStabilizer :
    IsCompact (L.localStabilizer p : Set (orthogonalGroup (L.norm.baseChange ℚ_[p]))) := by
  classical
  rw [L.localStabilizer_eq_integralOrthogonalSubgroup p (Free.chooseBasis ℤ L)]
  exact isCompact_integralOrthogonalSubgroup _ _

/-- For a fixed rational basis `b` of `V`, the local stabilizer of `L` is the integral orthogonal
subgroup of `b` at almost every prime. -/
theorem eventually_localStabilizer_eq {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Basis ι ℚ V) :
    ∀ᶠ p : Nat.Primes in cofinite,
      L.localStabilizer p =
        integralOrthogonalSubgroup (L.norm.baseChange ℚ_[p]) (b.baseChange ℚ_[p]) := by
  classical
  filter_upwards [eventually_integralOrthogonalSubgroup_baseChange_eq L.norm
    ((Free.chooseBasis ℤ L).extendOfIsLattice ℚ) b] with p hp
  rw [L.localStabilizer_eq_integralOrthogonalSubgroup p (Free.chooseBasis ℤ L)]
  exact hp

/-- **A rational isometry preserves `L` exactly when it lies in every local stabilizer.** The
rational isometries in `∏_p K_p(L)` are therefore the isometries of `L`. -/
theorem forall_orthogonalGroupBaseChange_mem_localStabilizer_iff (g : orthogonalGroup L.norm) :
    (∀ p : Nat.Primes, orthogonalGroupBaseChange (A := ℚ_[p]) L.norm g ∈ L.localStabilizer p) ↔
      ∀ x, (g : V ≃ₗ[ℚ] V) x ∈ L.carrier ↔ x ∈ L.carrier := by
  classical
  let e := Free.chooseBasis ℤ L
  let b := e.extendOfIsLattice ℚ
  -- Locally, membership is `p`-adic integrality of the rational matrices of `g` and `g⁻¹`.
  have hloc (p : Nat.Primes) :
      orthogonalGroupBaseChange (A := ℚ_[p]) L.norm g ∈ L.localStabilizer p ↔
        (∀ i j, ‖((LinearMap.toMatrix b b (g : V ≃ₗ[ℚ] V).toLinearMap i j : ℚ) : ℚ_[p])‖ ≤ 1) ∧
        ∀ i j, ‖((LinearMap.toMatrix b b
          ((g⁻¹ : orthogonalGroup L.norm) : V ≃ₗ[ℚ] V).toLinearMap i j : ℚ) : ℚ_[p])‖ ≤ 1 := by
    have h₁ := toMatrix_orthogonalGroupBaseChange (A := ℚ_[p]) L.norm b g
    have h₂ := toMatrix_orthogonalGroupBaseChange (A := ℚ_[p]) L.norm b g⁻¹
    rw [map_inv, Subgroup.coe_inv] at h₂
    rw [L.localStabilizer_eq_integralOrthogonalSubgroup p e,
      mem_integralOrthogonalSubgroup_iff_norm, h₁, h₂]
    simp only [Matrix.map_apply, eq_ratCast]
  -- Globally, preserving `L` is integrality of the same two matrices.
  have hint (f : V →ₗ[ℚ] V) : Set.MapsTo f L.carrier L.carrier ↔
      ∀ i j, (LinearMap.toMatrix b b f i j).den = 1 := by
    have h := b.mapsTo_span_range_iff_forall_toMatrix_mem (A := ℤ) f
    rw [e.span_range_extendOfIsLattice] at h
    rw [h]
    refine forall₂_congr fun i j ↦ ⟨?_, fun h ↦ ⟨_, (Rat.den_eq_one_iff _).mp h⟩⟩
    rintro ⟨n, hn⟩
    rw [← hn, algebraMap_int_eq, eq_intCast, Rat.den_intCast]
  have hglob : (∀ x, (g : V ≃ₗ[ℚ] V) x ∈ L.carrier ↔ x ∈ L.carrier) ↔
      Set.MapsTo (g : V ≃ₗ[ℚ] V).toLinearMap L.carrier L.carrier ∧
        Set.MapsTo ((g⁻¹ : orthogonalGroup L.norm) : V ≃ₗ[ℚ] V).toLinearMap L.carrier
          L.carrier := by
    simpa only [LinearEquiv.coe_toEquiv, LinearEquiv.coe_toEquiv_symm, EquivLike.coe_coe,
      LinearEquiv.coe_coe, SetLike.mem_coe, Subgroup.coe_inv, LinearEquiv.coe_inv] using
      Equiv.forall_apply_mem_iff_iff_mapsTo (g : V ≃ₗ[ℚ] V).toEquiv L.carrier L.carrier
  rw [hglob, hint, hint]
  -- A rational number is an integer exactly when it is a `p`-adic integer at every prime.
  simp only [hloc, forall_and, forall_comm (α := Nat.Primes),
    Padic.forall_norm_rat_le_one_iff_den_eq_one]

end Stabilizer

section CompactOpens

/-- The compatible compact-open tuple of a nondegenerate integral lattice: the integral family of a
basis of `L`, whose orthogonal reference subgroups are the local stabilizers `K_p(L)`
(`TauCeti.IntegralLattice.orthogonalCompactOpens_orthogonal`) and whose derived special orthogonal
subgroups are the proper local stabilizers `K_p⁺(L) = K_p(L) ∩ SO(V_p)`. -/
noncomputable def orthogonalCompactOpens [L.IsNondegenerate] : OrthogonalCompactOpens L.norm := by
  classical
  have := L.finiteDimensional
  exact OrthogonalCompactOpens.integral L.norm L.nondegenerate_norm L.rationalBasis

/-- The orthogonal reference subgroups of the compact-open tuple of `L` are its local
stabilizers. -/
@[simp]
theorem orthogonalCompactOpens_orthogonal [L.IsNondegenerate] (p : Nat.Primes) :
    L.orthogonalCompactOpens.orthogonal p = L.localStabilizer p := by
  classical
  rw [L.localStabilizer_eq_integralOrthogonalSubgroup p (Free.chooseBasis ℤ L)]
  have h : L.rationalBasis = (Free.chooseBasis ℤ L).extendOfIsLattice ℚ :=
    Basis.eq_of_apply_eq fun i ↦ by rw [rationalBasis_apply, Basis.extendOfIsLattice_apply]
  simp only [orthogonalCompactOpens, OrthogonalCompactOpens.integral_orthogonal, h]

end CompactOpens

end IntegralLattice

end TauCeti
