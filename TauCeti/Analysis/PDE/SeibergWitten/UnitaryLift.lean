/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.SeibergWitten.CanonicalLine
public import TauCeti.Geometry.Symplectic.AlmostComplex.UnitaryGroup
public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.CircleLift
import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.Surjectivity

/-!
# The canonical `Spinᶜ` lift of the unitary group

Let `V` be an oriented real inner product space of dimension four with an orthogonal complex
structure `J` inducing the orientation, witnessed by a positively oriented unitary frame
`(e₀, e₁, e₂, e₃)`, `J e₀ = e₁` and `J e₂ = e₃`, and let `ω` be its Kähler form. Let `W` be a
Hermitian spin module, `c(v) = ρ (ι Q v)` with `Q v = -‖v‖²`, whose positive half-spinors `W⁺`
have complex dimension two. In `W⁺` the `-2i`-eigenspace of `c₂(ω)` is Taubes's canonical line
`ℂ u₀`, the range of the projection `P_α`, and the `2i`-eigenspace is its complement.

An almost Hermitian four-manifold carries a canonical `Spinᶜ` structure, with spinor bundle
`W⁺ = Λ⁰'⁰ ⊕ Λ⁰'²` and determinant line `K⁻¹`. At the level of structure groups it is the
canonical homomorphism `U(2) → Spinᶜ(4)` lifting `U(2) ⊆ SO(4)`, and this file constructs it.
The rotations commuting with `J` form the unitary group `U(V, J)`
(`TauCeti.AlmostComplexStructure.unitaryGroup`). The elements of `Spinᶜ(4)` acting trivially on
the canonical line form a subgroup (`TauCeti.SeibergWitten.canonicalLineFixingSubgroup`), and
the rotation homomorphism `Spinᶜ(4) → SO(4)` maps it isomorphically onto `U(V, J)`:

* Its rotations commute with `J`. On the canonical line Clifford multiplication turns `J` into
  `i`, `c(J v) u₀ = i c(v) u₀`, and conversely this relation cuts out the canonical line
  (`TauCeti.SeibergWitten.cliffordProjection_kahlerForm_apply_eq_self_iff`). Clifford
  equivariance then gives `c(A J v) u₀ = c(J A v) u₀`, and `c(w) u₀ ≠ 0` for `w ≠ 0`.
* It meets the kernel of the rotation homomorphism trivially, since that kernel is the twisting
  circle `U(1) ⊆ Spinᶜ(4)`, which acts on the canonical line by scalars.
* It maps onto `U(V, J)`. A Spin lift `s` of a unitary rotation preserves the relation cutting
  out the canonical line, so acts on that line by a scalar `c`, of modulus one by unitarity;
  then `[s, c⁻¹]` fixes the line.

The inverse isomorphism is the canonical lift `TauCeti.SeibergWitten.unitaryLift`. Its
determinant character is the scalar by which it acts on the complementary line
(`spinCGroupHalfSpinRep_apply_eq_det_smul_of_mem_canonicalLineFixingSubgroup_of_bivectorExterior`),
because `Spinᶜ(4)` acts on `W⁺` with determinant its determinant character. For the complex line
`⟨e₂, e₃⟩`, the canonical lift of its rotations is the `Spinᶜ` lift `CliffordAlgebra.spinCCircle`
of the rotations of that oriented plane
(`TauCeti.SeibergWitten.unitaryLift_toSpecialOrthogonal_spinCCircle`): on the canonical line
`c(e₀) c(e₁)` acts by `-i`, where `spinCCircle` has weight one.

The subgroup fixing the canonical line is defined through the given spin module `W`. The
identification of the determinant character with the complex determinant of the unitary rotation
is not made here.

## Main definitions

* `TauCeti.SeibergWitten.canonicalLineFixingSubgroup o ρ J hQ₀`: the elements of `Spinᶜ(4)`
  acting trivially on the canonical line.
* `TauCeti.SeibergWitten.canonicalLineFixingSubgroupEquiv`: the rotation homomorphism, as an
  isomorphism of that subgroup onto `U(V, J)`.
* `TauCeti.SeibergWitten.unitaryLift`: the canonical lift `U(V, J) → Spinᶜ(4)`.

## Main results

* `toSpecialOrthogonal_mem_unitaryGroup_of_mem_canonicalLineFixingSubgroup`,
  `eq_one_of_mem_canonicalLineFixingSubgroup_of_toSpecialOrthogonal_eq_one` and
  `exists_mem_canonicalLineFixingSubgroup_toSpecialOrthogonal_eq_of_mem_unitaryGroup`: the three
  steps above, combined in `TauCeti.SeibergWitten.canonicalLineFixingSubgroupEquiv`.
* `TauCeti.SeibergWitten.toSpecialOrthogonal_unitaryLift` and
  `TauCeti.SeibergWitten.eq_unitaryLift_iff`: the canonical lift lifts `U(V, J) ⊆ SO(4)`, and is
  the unique such lift fixing the canonical line.
* `spinCGroupHalfSpinRep_apply_eq_det_smul_of_mem_canonicalLineFixingSubgroup_of_bivectorExterior`:
  an element fixing the canonical line acts on the complementary line by its determinant
  character.
* `TauCeti.SeibergWitten.unitaryLift_toSpecialOrthogonal_spinCCircle`: comparison with
  `spinCCircle` on the complex line `⟨e₂, e₃⟩`.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Appendix D.
* J. W. Morgan, *The Seiberg–Witten equations and applications to the topology of smooth
  four-manifolds*, Mathematical Notes 44, Princeton University Press, 1996, §3.4.
* C. H. Taubes, *The Seiberg–Witten invariants and symplectic forms*, Math. Res. Lett. 1 (1994),
  809–822.
-/

public section

noncomputable section

open CliffordAlgebra Module Module.End
open scoped RealInnerProductSpace InnerProductSpace

namespace TauCeti.SeibergWitten

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [Fact (finrank ℝ V = 4)]
  {Q : QuadraticForm ℝ V} {o : Orientation ℝ V (Fin 4)}

attribute [local instance] finiteDimensional_of_finrank_four

/-! ### The subgroup of `Spinᶜ(4)` fixing the canonical line -/

section FixingSubgroup

variable {W : Type*} [AddCommGroup W] [Module ℂ W] {ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ W}
  {e : OrthonormalBasis (Fin 4) ℝ V} {J : AlmostComplexStructure V}
  (hQ : ∀ v, Q v = -‖v‖ ^ 2) (he : e.toBasis.orientation = o)
  (h₀ : J (e 0) = e 1) (h₂ : J (e 2) = e 3)
  (hQ₀ : Q ≠ 0)

variable (o ρ J) in
/-- **The subgroup fixing the canonical line**: the elements of `Spinᶜ(4)` acting trivially on
the `-2i`-eigenspace of `c₂(ω)` in the positive half-spinors, Taubes's line `ℂ u₀`. -/
def canonicalLineFixingSubgroup : Subgroup (spinCGroup Q hQ₀) where
  carrier := {x | ∀ ψ : eigenspace (ρ (chirality Q o)) 1,
    ρ (bivectorExterior Q J.kahlerForm) ψ = (-2 * Complex.I) • (ψ : W) →
      spinCGroupHalfSpinRep o ρ 1 hQ₀ x ψ = ψ}
  mul_mem' {x y} hx hy ψ hψ := by
    rw [map_mul, mul_apply_eq_comp, hy ψ hψ, hx ψ hψ]
  one_mem' ψ _ := by simp
  inv_mem' {x} hx ψ hψ := by
    conv_lhs => rw [← hx ψ hψ]
    rw [← mul_apply_eq_comp, ← map_mul, inv_mul_cancel, map_one, one_apply_eq_self]

/-- Membership in the subgroup fixing the canonical line. -/
theorem mem_canonicalLineFixingSubgroup_iff {x : spinCGroup Q hQ₀} :
    x ∈ canonicalLineFixingSubgroup o ρ J hQ₀ ↔
      ∀ ψ : eigenspace (ρ (chirality Q o)) 1,
        ρ (bivectorExterior Q J.kahlerForm) ψ = (-2 * Complex.I) • (ψ : W) →
          spinCGroupHalfSpinRep o ρ 1 hQ₀ x ψ = ψ :=
  Iff.rfl

/-- A relation `c(w) ψ = μ c(v) ψ` in `W` on a positive half-spinor `ψ` is the same relation
between the half-spin Clifford multiplications `W⁺ → W⁻` by `w` and `v`. -/
private theorem halfSpinCliffordMul_apply_eq_smul {ψ : eigenspace (ρ (chirality Q o)) 1} {μ : ℂ}
    {v w : V} (h : ρ (ι Q w) ψ = μ • ρ (ι Q v) ψ) :
    halfSpinCliffordMul o ρ 1 w ψ = μ • halfSpinCliffordMul o ρ 1 v ψ :=
  Subtype.ext (by simpa using h)

/-- An element of `Spinᶜ(4)` whose rotation commutes with `J` preserves each relation
`c(J v) ψ = μ c(v) ψ`. -/
private theorem ι_apply_apply_spinCGroupHalfSpinRep {x : spinCGroup Q hQ₀}
    (hx : spinCGroup.toSpecialOrthogonal Q hQ₀ x ∈ J.unitaryGroup Q) {μ : ℂ}
    {ψ : eigenspace (ρ (chirality Q o)) 1} (hψ : ∀ v, ρ (ι Q (J v)) ψ = μ • ρ (ι Q v) ψ)
    (v : V) :
    ρ (ι Q (J v)) (spinCGroupHalfSpinRep o ρ 1 hQ₀ x ψ) =
      μ • ρ (ι Q v) (spinCGroupHalfSpinRep o ρ 1 hQ₀ x ψ) := by
  obtain ⟨w, rfl⟩ := (spinCGroup.toSpecialOrthogonal Q hQ₀ x : V ≃ₗ[ℝ] V).surjective v
  rw [← AlmostComplexStructure.mem_unitaryGroup_iff.1 hx w, ι_apply_spinCGroupHalfSpinRep_apply,
    ι_apply_spinCGroupHalfSpinRep_apply, halfSpinCliffordMul_apply_eq_smul (hψ w), map_smul,
    Submodule.coe_smul]

include hQ he h₀ h₂ in
/-- **The `Spinᶜ` lift of the rotations of the complex line `⟨e₂, e₃⟩` fixes the canonical line.**
On a positive half-spinor `c₂(ω) = c(e₀) c(e₁) + c(e₂) c(e₃)` acts as `2 c(e₀) c(e₁)`, so on the
canonical line `c(e₀) c(e₁)` acts by `-i`, where `spinCCircle` has weight one. -/
@[simp]
theorem spinCCircle_mem_canonicalLineFixingSubgroup (z : Circle) :
    spinCCircle Q hQ₀ (e 2) (e 3) (e.isOrtho_apply hQ (by decide))
      (e.map_apply_mul_map_apply hQ 2 3) z ∈ canonicalLineFixingSubgroup o ρ J hQ₀ := by
  intro ψ hψ
  rw [AlmostComplexStructure.bivectorExterior_kahlerForm hQ h₀ h₂, map_add, LinearMap.add_apply,
    map_ι_mul_ι_two_three_apply e hQ ρ he ψ.2, one_smul] at hψ
  have h : ρ (ι Q (e 0) * ι Q (e 1)) ψ = -Complex.I • (ψ : W) := by
    linear_combination (norm := module) (2⁻¹ : ℂ) • hψ
  exact Subtype.ext
    (coe_spinCGroupHalfSpinRep_one_spinCCircle_apply_of_eq_neg_I_smul hQ₀ e hQ he ρ z h)

end FixingSubgroup

/-! ### The canonical lift -/

section Hermitian

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
  {ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ W}
  {e : OrthonormalBasis (Fin 4) ℝ V} {J : AlmostComplexStructure V}
  (hQ : ∀ v, Q v = -‖v‖ ^ 2) (he : e.toBasis.orientation = o)
  (h₀ : J (e 0) = e 1) (h₂ : J (e 2) = e 3)

variable (o ρ) in
/-- The positive half-spinors are the `1`-eigenspace of the chirality, the domain of
`spinCGroupHalfSpinRep`: `positiveHalfSpinors_eq_eigenspace` as a linear equivalence. -/
private abbrev positiveHalfSpinorsEquiv :
    positiveHalfSpinors o ρ ≃ₗ[ℂ] eigenspace (ρ (chirality Q o)) 1 :=
  LinearEquiv.ofEq _ _ (positiveHalfSpinors_eq_eigenspace o ρ)

section Lift

variable (hQ₀ : Q ≠ 0) (hW : finrank ℂ (positiveHalfSpinors o ρ) = 2)

include hQ he h₀ h₂ hW in
/-- The canonical line is spanned by a nonzero `u` with `P_α u = u`. -/
private theorem exists_ne_zero_cliffordProjection_kahlerForm_apply_eq_self_forall_eq_smul :
    ∃ u : positiveHalfSpinors o ρ, u ≠ 0 ∧ cliffordProjection o ρ J.kahlerForm u = u ∧
      ∀ ψ, cliffordProjection o ρ J.kahlerForm ψ = ψ → ∃ c : ℂ, ψ = c • u :=
  have hkl : 2 + 2 = finrank ℝ V := (Fact.out : finrank ℝ V = 4).symm
  exists_ne_zero_cliffordProjection_apply_eq_self_forall_eq_smul o ρ hQ hkl
    (AlmostComplexStructure.hodgeStar_kahlerForm h₀ h₂ hkl he)
    (AlmostComplexStructure.norm_kahlerForm_sq_eq_two
      (AlmostComplexStructure.inner_apply_apply_of_orthonormalBasis h₀ h₂)) hW

include hQ he h₀ h₂ hW in
/-- **An element fixing the canonical line rotates `V` complex linearly**: its rotation commutes
with `J`. -/
theorem toSpecialOrthogonal_mem_unitaryGroup_of_mem_canonicalLineFixingSubgroup
    {x : spinCGroup Q hQ₀} (hx : x ∈ canonicalLineFixingSubgroup o ρ J hQ₀) :
    spinCGroup.toSpecialOrthogonal Q hQ₀ x ∈ J.unitaryGroup Q := by
  have hkl : 2 + 2 = finrank ℝ V := (Fact.out : finrank ℝ V = 4).symm
  obtain ⟨u, hu₀, hu, -⟩ :=
    exists_ne_zero_cliffordProjection_kahlerForm_apply_eq_self_forall_eq_smul hQ he h₀ h₂ hW
  set u' := positiveHalfSpinorsEquiv o ρ u
  have hxu : spinCGroupHalfSpinRep o ρ 1 hQ₀ x u' = u' :=
    hx u' (bivectorExterior_apply_of_cliffordProjection_apply_eq_self o ρ hu)
  have hcl := ι_apply_apply_of_cliffordProjection_apply_eq_self hQ hkl he h₀ h₂ hu
  rw [AlmostComplexStructure.mem_unitaryGroup_iff]
  intro v
  set A := (spinCGroup.toSpecialOrthogonal Q hQ₀ x : V ≃ₗ[ℝ] V)
  -- `c(A (J v)) u = x (c(J v) u) = x (i c(v) u) = i c(A v) u = c(J (A v)) u`.
  have h1 := ι_apply_spinCGroupHalfSpinRep_apply o ρ 1 hQ₀ x (J v) u'
  have h2 := ι_apply_spinCGroupHalfSpinRep_apply o ρ 1 hQ₀ x v u'
  rw [hxu] at h1 h2
  rw [halfSpinCliffordMul_apply_eq_smul (ψ := u') (hcl v), map_smul, Submodule.coe_smul,
    ← h2] at h1
  exact map_ι_apply_left_injective ρ (fun w hw ↦ by simpa [hQ] using hw)
    (by simpa using hu₀ : (u : W) ≠ 0) (h1.trans (hcl (A v)).symm)

include hQ he h₀ h₂ hW in
/-- **Only the identity fixes the canonical line and acts trivially on `V`**: the kernel of the
rotation homomorphism is the twisting circle, which acts on the canonical line by scalars. -/
theorem eq_one_of_mem_canonicalLineFixingSubgroup_of_toSpecialOrthogonal_eq_one
    {x : spinCGroup Q hQ₀} (hx : x ∈ canonicalLineFixingSubgroup o ρ J hQ₀)
    (h1 : spinCGroup.toSpecialOrthogonal Q hQ₀ x = 1) : x = 1 := by
  have hQn : Q.Nondegenerate :=
    QuadraticMap.Anisotropic.nondegenerate fun v hv ↦ by simpa [hQ] using hv
  have : Nontrivial V := Module.nontrivial_of_finrank_eq_succ (Fact.out : finrank ℝ V = 4)
  -- The kernel of the rotation homomorphism is the twisting circle.
  obtain ⟨w, rfl⟩ : ∃ w : Circle, spinCGroup.ofCircle Q hQ₀ w = x := by
    obtain ⟨⟨s, z⟩, rfl⟩ := spinCGroup.mk_surjective Q hQ₀ x
    rw [spinCGroup.toSpecialOrthogonal_mk] at h1
    rcases (mem_ker_spinToSpecialOrthogonal_iff Q hQn s).1 h1 with rfl | rfl
    · exact ⟨z, by rw [← spinCGroup.ofSpin_mul_ofCircle, map_one, one_mul]⟩
    · exact ⟨-1 * z, by rw [← spinCGroup.ofSpin_mul_ofCircle, spinCGroup.ofSpin_negOne, map_mul]⟩
  -- It acts on a nonzero vector of the canonical line by `w`.
  obtain ⟨u, hu₀, hu, -⟩ :=
    exists_ne_zero_cliffordProjection_kahlerForm_apply_eq_self_forall_eq_smul hQ he h₀ h₂ hW
  have h := congrArg Subtype.val (hx (positiveHalfSpinorsEquiv o ρ u)
    (bivectorExterior_apply_of_cliffordProjection_apply_eq_self o ρ hu))
  rw [spinCGroupHalfSpinRep_ofCircle, LinearMap.smul_apply, one_apply_eq_self,
    Submodule.coe_smul, LinearEquiv.coe_ofEq_apply] at h
  have hw : (w : ℂ) = 1 := by
    have h' : ((w : ℂ) - 1) • (u : W) = 0 := by rw [sub_smul, h, one_smul, sub_self]
    exact sub_eq_zero.1 ((smul_eq_zero.1 h').resolve_right (by simpa using hu₀))
  rw [Circle.coe_eq_one.1 hw, map_one]

include hQ he h₀ h₂ hW in
/-- **Every unitary rotation lifts to the subgroup fixing the canonical line.** A Spin lift `s` of
the rotation moves the canonical line to itself and acts on it by a unit scalar `c`; then
`[s, c⁻¹]` fixes the line. -/
theorem exists_mem_canonicalLineFixingSubgroup_toSpecialOrthogonal_eq_of_mem_unitaryGroup
    (hρ : ∀ v, LinearMap.adjoint (ρ (ι Q v)) = -ρ (ι Q v))
    {A : TauCeti.QuadraticMap.specialOrthogonalGroup Q} (hA : A ∈ J.unitaryGroup Q) :
    ∃ x ∈ canonicalLineFixingSubgroup o ρ J hQ₀, spinCGroup.toSpecialOrthogonal Q hQ₀ x = A := by
  have hQn : Q.Nondegenerate :=
    QuadraticMap.Anisotropic.nondegenerate fun v hv ↦ by simpa [hQ] using hv
  obtain ⟨s, hs⟩ := spinToSpecialOrthogonal_surjective_of_isSquare Q hQn (fun v _ ↦ by
    rw [invOf_eq_inv, hQ]
    exact ⟨‖v‖⁻¹, by ring⟩) A
  obtain ⟨u, hu₀, hu, hspan⟩ :=
    exists_ne_zero_cliffordProjection_kahlerForm_apply_eq_self_forall_eq_smul hQ he h₀ h₂ hW
  set x₀ := spinCGroup.ofSpin Q hQ₀ s
  set u' := positiveHalfSpinorsEquiv o ρ u
  have hx₀ : spinCGroup.toSpecialOrthogonal Q hQ₀ x₀ ∈ J.unitaryGroup Q := by
    rwa [spinCGroup.toSpecialOrthogonal_ofSpin, hs]
  -- `x₀` moves the canonical line to itself, so `x₀ u = c u`.
  have hP := (cliffordProjection_kahlerForm_apply_eq_self_iff hQ he h₀ h₂
    (ψ := (positiveHalfSpinorsEquiv o ρ).symm (spinCGroupHalfSpinRep o ρ 1 hQ₀ x₀ u'))).2
    (ι_apply_apply_spinCGroupHalfSpinRep hQ₀ hx₀
      ((cliffordProjection_kahlerForm_apply_eq_self_iff hQ he h₀ h₂).1 hu))
  obtain ⟨c, hc⟩ := hspan _ hP
  have hc' : (spinCGroupHalfSpinRep o ρ 1 hQ₀ x₀ u' : W) = c • (u' : W) := by
    rw [(positiveHalfSpinorsEquiv o ρ).symm_apply_eq.1 hc, map_smul, Submodule.coe_smul]
  -- The action is unitary, so `‖c‖ = 1`.
  have hnorm : ‖c‖ = 1 := by
    have hi := inner_spinCGroupHalfSpinRep_apply_spinCGroupHalfSpinRep_apply o 1 hρ hQ₀ x₀ u' u'
    rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at hi
    have hn : ‖(spinCGroupHalfSpinRep o ρ 1 hQ₀ x₀ u' : W)‖ = ‖(u' : W)‖ := by
      have := (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1
        (by exact_mod_cast hi : ‖spinCGroupHalfSpinRep o ρ 1 hQ₀ x₀ u'‖ ^ 2 = ‖u'‖ ^ 2)
      simpa using this
    rw [hc', norm_smul] at hn
    exact (mul_eq_right₀ (by simpa [u'] using hu₀)).1 hn
  set z : Circle := ⟨c, mem_sphere_zero_iff_norm.2 hnorm⟩
  -- The coercion of `z` to `ℂ` is the scalar `c` it was built from.
  have hz : (z : ℂ) = c := rfl
  refine ⟨x₀ * spinCGroup.ofCircle Q hQ₀ z⁻¹, fun ψ hψ ↦ ?_, by
    rw [map_mul, spinCGroup.toSpecialOrthogonal_ofCircle, mul_one,
      spinCGroup.toSpecialOrthogonal_ofSpin, hs]⟩
  obtain ⟨d, hd⟩ := hspan _ (cliffordProjection_apply_eq_self_of_bivectorExterior_apply o ρ
    (ψ := (positiveHalfSpinorsEquiv o ρ).symm ψ) hψ)
  have hd' : ψ = d • u' := by rw [(positiveHalfSpinorsEquiv o ρ).symm_apply_eq.1 hd, map_smul]
  have hc0 : c ≠ 0 := by rintro rfl; simp at hnorm
  rw [map_mul, mul_apply_eq_comp, spinCGroupHalfSpinRep_ofCircle, LinearMap.smul_apply,
    one_apply_eq_self, hd', map_smul, map_smul, Subtype.ext_iff]
  simp only [Submodule.coe_smul, hc', smul_smul, Circle.coe_inv]
  rw [hz, mul_comm c⁻¹ d, mul_assoc, inv_mul_cancel₀ hc0, mul_one]

/-- **The subgroup fixing the canonical line is the unitary group**: the rotation homomorphism
`Spinᶜ(4) → SO(4)` restricts to an isomorphism from the subgroup fixing the canonical line onto
the rotations commuting with `J`. -/
def canonicalLineFixingSubgroupEquiv (hρ : ∀ v, LinearMap.adjoint (ρ (ι Q v)) = -ρ (ι Q v)) :
    canonicalLineFixingSubgroup o ρ J hQ₀ ≃* J.unitaryGroup Q :=
  MulEquiv.ofBijective (((spinCGroup.toSpecialOrthogonal Q hQ₀).comp
      (canonicalLineFixingSubgroup o ρ J hQ₀).subtype).codRestrict (J.unitaryGroup Q)
        fun x ↦ toSpecialOrthogonal_mem_unitaryGroup_of_mem_canonicalLineFixingSubgroup
          hQ he h₀ h₂ hQ₀ hW x.2) <| by
    refine ⟨(injective_iff_map_eq_one _).2 fun x hx ↦ Subtype.ext ?_, fun A ↦ ?_⟩
    · exact eq_one_of_mem_canonicalLineFixingSubgroup_of_toSpecialOrthogonal_eq_one hQ he h₀ h₂
        hQ₀ hW x.2 (congrArg Subtype.val hx)
    · obtain ⟨x, hx, hxA⟩ :=
        exists_mem_canonicalLineFixingSubgroup_toSpecialOrthogonal_eq_of_mem_unitaryGroup
          hQ he h₀ h₂ hQ₀ hW hρ A.2
      exact ⟨⟨x, hx⟩, Subtype.ext hxA⟩

/-- The isomorphism `canonicalLineFixingSubgroupEquiv` is the rotation homomorphism. -/
@[simp]
theorem coe_canonicalLineFixingSubgroupEquiv_apply
    (hρ : ∀ v, LinearMap.adjoint (ρ (ι Q v)) = -ρ (ι Q v))
    (x : canonicalLineFixingSubgroup o ρ J hQ₀) :
    (canonicalLineFixingSubgroupEquiv hQ he h₀ h₂ hQ₀ hW hρ x :
      TauCeti.QuadraticMap.specialOrthogonalGroup Q) = spinCGroup.toSpecialOrthogonal Q hQ₀ x :=
  (rfl)

/-- **The canonical `Spinᶜ` lift of the unitary group** `U(V, J) → Spinᶜ(4)`: the inverse of the
rotation homomorphism on the subgroup fixing the canonical line. It lifts the inclusion
`U(V, J) ⊆ SO(4)` (`toSpecialOrthogonal_unitaryLift`) and is characterized among such lifts by
acting trivially on the canonical line (`eq_unitaryLift_iff`); its determinant character is the
scalar by which it acts on the complementary line
(`spinCGroupHalfSpinRep_apply_eq_det_smul_of_mem_canonicalLineFixingSubgroup_of_bivectorExterior`).
-/
def unitaryLift (hρ : ∀ v, LinearMap.adjoint (ρ (ι Q v)) = -ρ (ι Q v)) :
    J.unitaryGroup Q →* spinCGroup Q hQ₀ :=
  (canonicalLineFixingSubgroup o ρ J hQ₀).subtype.comp
    (canonicalLineFixingSubgroupEquiv hQ he h₀ h₂ hQ₀ hW hρ).symm.toMonoidHom

variable (hρ : ∀ v, LinearMap.adjoint (ρ (ι Q v)) = -ρ (ι Q v))

/-- The canonical lift fixes the canonical line. -/
@[simp]
theorem unitaryLift_mem_canonicalLineFixingSubgroup (A : J.unitaryGroup Q) :
    unitaryLift hQ he h₀ h₂ hQ₀ hW hρ A ∈ canonicalLineFixingSubgroup o ρ J hQ₀ :=
  ((canonicalLineFixingSubgroupEquiv hQ he h₀ h₂ hQ₀ hW hρ).symm A).2

/-- **The canonical lift lifts the inclusion `U(V, J) ⊆ SO(4)`**: the rotation of
`unitaryLift A` is `A`. -/
@[simp]
theorem toSpecialOrthogonal_unitaryLift (A : J.unitaryGroup Q) :
    spinCGroup.toSpecialOrthogonal Q hQ₀ (unitaryLift hQ he h₀ h₂ hQ₀ hW hρ A) = A :=
  congrArg Subtype.val
    ((canonicalLineFixingSubgroupEquiv hQ he h₀ h₂ hQ₀ hW hρ).apply_symm_apply A)

/-- **Characterization of the canonical lift**: `x` is the canonical lift of `A` exactly when it
fixes the canonical line and has rotation `A`. -/
theorem eq_unitaryLift_iff {x : spinCGroup Q hQ₀} {A : J.unitaryGroup Q} :
    x = unitaryLift hQ he h₀ h₂ hQ₀ hW hρ A ↔
      x ∈ canonicalLineFixingSubgroup o ρ J hQ₀ ∧ spinCGroup.toSpecialOrthogonal Q hQ₀ x = A := by
  refine ⟨fun h ↦ h ▸ ⟨unitaryLift_mem_canonicalLineFixingSubgroup hQ he h₀ h₂ hQ₀ hW hρ A,
    toSpecialOrthogonal_unitaryLift hQ he h₀ h₂ hQ₀ hW hρ A⟩, fun ⟨hx, hxA⟩ ↦ ?_⟩
  have h := (canonicalLineFixingSubgroupEquiv hQ he h₀ h₂ hQ₀ hW hρ).symm_apply_apply ⟨x, hx⟩
  have hA : canonicalLineFixingSubgroupEquiv hQ he h₀ h₂ hQ₀ hW hρ ⟨x, hx⟩ = A :=
    Subtype.ext hxA
  rw [hA] at h
  exact (congrArg Subtype.val h).symm

/-- An element fixing the canonical line is the canonical lift of its rotation. -/
@[simp]
theorem unitaryLift_toSpecialOrthogonal_of_mem_canonicalLineFixingSubgroup {x : spinCGroup Q hQ₀}
    (hx : x ∈ canonicalLineFixingSubgroup o ρ J hQ₀) :
    unitaryLift hQ he h₀ h₂ hQ₀ hW hρ
        ⟨spinCGroup.toSpecialOrthogonal Q hQ₀ x,
          toSpecialOrthogonal_mem_unitaryGroup_of_mem_canonicalLineFixingSubgroup
            hQ he h₀ h₂ hQ₀ hW hx⟩ = x :=
  ((eq_unitaryLift_iff hQ he h₀ h₂ hQ₀ hW hρ).2 ⟨hx, rfl⟩).symm

end Lift

/-! ### The determinant character on the complementary line -/

section Det

variable (hQ₀ : Q ≠ 0) (hW : finrank ℂ (positiveHalfSpinors o ρ) = 2)

include hQ he h₀ h₂ hW in
/-- **The determinant character is the action on the complementary line.** An element `x` of
`Spinᶜ(4)` fixing the canonical line acts on the complementary line, the `2i`-eigenspace of
`c₂(ω)` in the positive half-spinors, by its determinant character `det x`. -/
theorem
    spinCGroupHalfSpinRep_apply_eq_det_smul_of_mem_canonicalLineFixingSubgroup_of_bivectorExterior
    {x : spinCGroup Q hQ₀} (hx : x ∈ canonicalLineFixingSubgroup o ρ J hQ₀)
    {β : eigenspace (ρ (chirality Q o)) 1}
    (hβ : ρ (bivectorExterior Q J.kahlerForm) β = (2 * Complex.I) • (β : W)) :
    spinCGroupHalfSpinRep o ρ 1 hQ₀ x β = (spinCGroup.det Q hQ₀ x : ℂ) • β := by
  have hkl : 2 + 2 = finrank ℝ V := (Fact.out : finrank ℝ V = 4).symm
  obtain ⟨u, hu₀, hu, -⟩ :=
    exists_ne_zero_cliffordProjection_kahlerForm_apply_eq_self_forall_eq_smul hQ he h₀ h₂ hW
  obtain ⟨u', hu'₀, hu', hspan'⟩ :=
    exists_ne_zero_cliffordProjection_apply_eq_zero_forall_eq_smul o ρ hQ hkl
      (AlmostComplexStructure.hodgeStar_kahlerForm h₀ h₂ hkl he)
      (AlmostComplexStructure.norm_kahlerForm_sq_eq_two
        (AlmostComplexStructure.inner_apply_apply_of_orthonormalBasis h₀ h₂)) hW
  set v := positiveHalfSpinorsEquiv o ρ u
  set v' := positiveHalfSpinorsEquiv o ρ u'
  have hxA := toSpecialOrthogonal_mem_unitaryGroup_of_mem_canonicalLineFixingSubgroup
    hQ he h₀ h₂ hQ₀ hW hx
  -- `x` fixes `u` and moves `u'` to a multiple `c u'` of itself.
  have hxv : spinCGroupHalfSpinRep o ρ 1 hQ₀ x v = v :=
    hx v (bivectorExterior_apply_of_cliffordProjection_apply_eq_self o ρ hu)
  obtain ⟨c, hc⟩ :=
    hspan' ((positiveHalfSpinorsEquiv o ρ).symm (spinCGroupHalfSpinRep o ρ 1 hQ₀ x v'))
    ((cliffordProjection_kahlerForm_apply_eq_zero_iff hQ he h₀ h₂).2
      (ι_apply_apply_spinCGroupHalfSpinRep hQ₀ hxA
        ((cliffordProjection_kahlerForm_apply_eq_zero_iff hQ he h₀ h₂).1 hu')))
  have hxv' : spinCGroupHalfSpinRep o ρ 1 hQ₀ x v' = c • v' := by
    rw [(positiveHalfSpinorsEquiv o ρ).symm_apply_eq.1 hc, map_smul]
  -- Computing the determinant in the basis `(u, u')` identifies `c` with `det x`.
  have hli : LinearIndependent ℂ ![v, v'] := by
    refine LinearIndependent.pair_iff.2 fun s t hst ↦ ?_
    have hst' : s • u + t • u' = 0 :=
      (positiveHalfSpinorsEquiv o ρ).injective (by rwa [map_add, map_smul, map_smul, map_zero])
    have hs := congrArg (cliffordProjection o ρ J.kahlerForm) hst'
    rw [map_add, map_smul, map_smul, hu, hu', smul_zero, add_zero, map_zero] at hs
    have hs0 : s = 0 := (smul_eq_zero.1 hs).resolve_right hu₀
    rw [hs0, zero_smul, zero_add] at hst'
    exact ⟨hs0, (smul_eq_zero.1 hst').resolve_right hu'₀⟩
  have hW' : finrank ℂ (eigenspace (ρ (chirality Q o)) 1) = 2 :=
    (positiveHalfSpinorsEquiv o ρ).finrank_eq.symm.trans hW
  have hdet := det_spinCGroupHalfSpinRep o ρ 1 hQ₀ hQ hW' x
  set b := basisOfLinearIndependentOfCardEqFinrank hli (by simp [hW'])
  have hT0 : spinCGroupHalfSpinRep o ρ 1 hQ₀ x (b 0) = b 0 := by simpa [b] using hxv
  have hT1 : spinCGroupHalfSpinRep o ρ 1 hQ₀ x (b 1) = c • b 1 := by simpa [b] using hxv'
  rw [← LinearMap.det_toMatrix b, Matrix.det_fin_two] at hdet
  simp only [LinearMap.toMatrix_apply, hT0, hT1, map_smul, b.repr_self, Finsupp.single_eq_same,
    Finsupp.smul_single, smul_eq_mul, mul_one, Finsupp.single_eq_of_ne zero_ne_one,
    Finsupp.single_eq_of_ne one_ne_zero, mul_zero, sub_zero, one_mul] at hdet
  -- Every vector of the complementary line is a multiple of `u'`.
  obtain ⟨d, hd⟩ := hspan' _ (cliffordProjection_apply_eq_zero_of_bivectorExterior_apply o ρ
    (ψ := (positiveHalfSpinorsEquiv o ρ).symm β) hβ)
  have hd' : β = d • v' := by rw [(positiveHalfSpinorsEquiv o ρ).symm_apply_eq.1 hd, map_smul]
  rw [hd', map_smul, hxv', ← hdet, smul_comm]

end Det

/-! ### Comparison with the lift of the rotations of a complex line -/

section Circle

variable (hQ₀ : Q ≠ 0) (hW : finrank ℂ (positiveHalfSpinors o ρ) = 2)
  (hρ : ∀ v, LinearMap.adjoint (ρ (ι Q v)) = -ρ (ι Q v))

/-- **The canonical lift restricts to `spinCCircle` on the complex line `⟨e₂, e₃⟩`**: the
canonical lift of the rotation of `⟨e₂, e₃⟩` by `z` is `spinCCircle z`, the `Spinᶜ` lift of the
rotations of that oriented plane. -/
theorem unitaryLift_toSpecialOrthogonal_spinCCircle (z : Circle) :
    unitaryLift hQ he h₀ h₂ hQ₀ hW hρ
        ⟨spinCGroup.toSpecialOrthogonal Q hQ₀ (spinCCircle Q hQ₀ (e 2) (e 3)
            (e.isOrtho_apply hQ (by decide)) (e.map_apply_mul_map_apply hQ 2 3) z),
          toSpecialOrthogonal_mem_unitaryGroup_of_mem_canonicalLineFixingSubgroup
            hQ he h₀ h₂ hQ₀ hW (spinCCircle_mem_canonicalLineFixingSubgroup hQ he h₀ h₂ hQ₀ z)⟩ =
      spinCCircle Q hQ₀ (e 2) (e 3) (e.isOrtho_apply hQ (by decide))
        (e.map_apply_mul_map_apply hQ 2 3) z :=
  unitaryLift_toSpecialOrthogonal_of_mem_canonicalLineFixingSubgroup hQ he h₀ h₂ hQ₀ hW hρ
    (spinCCircle_mem_canonicalLineFixingSubgroup hQ he h₀ h₂ hQ₀ z)

end Circle

end Hermitian

end TauCeti.SeibergWitten
