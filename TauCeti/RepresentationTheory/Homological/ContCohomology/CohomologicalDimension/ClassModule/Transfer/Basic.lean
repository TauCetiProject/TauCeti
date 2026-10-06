/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.CohomologicalDimension.ClassModule.Basic
public import TauCeti.Topology.Algebra.Group.Transfer
import TauCeti.Topology.Algebra.Group.TopologicalAbelianization.Lift

/-!
# Transfer to the pro-p class module

For a finite-index subgroup `V` of a topological group `G`, the transfer to `V^ab(p)` is
Mathlib's `MonoidHom.transfer` applied to the canonical map `V → V^ab(p)`. It is continuous
when `V` is open; for profinite `G` it then kills the kernel of `G → G^ab(p)`. For normal
`V`, its restriction to `V` is the norm for the conjugation action of `G ⧸ V`. Its value on a
quotient representative is the sum of the factor set `abelianizationProPFactorSet` in the first
variable.

These formulas connect the group-theoretic transfer with the extension class
`abelianizationProPClass`: in particular, they identify the norm and the representative sum
that occur in the cyclic-quotient calculation of that class. No cohomological-dimension
hypothesis is needed for the formulas, and no claim of injectivity or surjectivity is made.

## References

* J. Neukirch, A. Schmidt and K. Wingberg, *Cohomology of Number Fields*, 2nd ed.,
  (1.5.9) and the transfer diagram (3.6.2).
* Transfer API: `TauCeti.transfer_eq_prod_lWord`, `TauCeti.continuous_transfer`, and
  `MonoidHom.transfer_eq_prod_mul_out`.
-/

public section

namespace TauCeti

open ContCohomology

variable (p : ℕ) (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (V : Subgroup G) [V.FiniteIndex]

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

/-- The transfer `G → V^ab(p)` induced by the canonical map `V → V^ab(p)`. -/
noncomputable def abelianizationProPTransfer : G →* abelianizationProP p G V :=
  MonoidHom.transfer (abelianizationProPMk p G V)

/-- The transfer to `V^ab(p)` is Mathlib's transfer of the canonical map `V → V^ab(p)`. -/
theorem abelianizationProPTransfer_def :
    abelianizationProPTransfer p G V = MonoidHom.transfer (abelianizationProPMk p G V) :=
  (rfl)

/-- The transfer is the product of the classes of the transversal words, for every transversal.
The representatives are arbitrary; the transfer itself does not depend on them. -/
theorem abelianizationProPTransfer_eq_prod_lWord (t : G ⧸ V → G)
    (ht : ∀ q : G ⧸ V, (QuotientGroup.mk (t q) : G ⧸ V) = q) (g : G) :
    abelianizationProPTransfer p G V g =
      ∏ q : G ⧸ V, abelianizationProPMk p G V ⟨lWord V t q g, lWord_mem V t ht q g⟩ := by
  unfold abelianizationProPTransfer
  exact transfer_eq_prod_lWord t ht _ g

/-- Transfer to `V^ab(p)` is continuous when `V` is open. Compactness and primality of `p`
are not required. -/
theorem continuous_abelianizationProPTransfer (hV : IsOpen (V : Set G)) :
    Continuous (abelianizationProPTransfer p G V) := by
  unfold abelianizationProPTransfer
  exact continuous_transfer hV (continuous_abelianizationProPMk p G V)

variable {p G V} in
/-- The transfer `Ver : G → V^ab(p)` kills the kernel of the canonical map `G → G^ab(p)`. It is a
continuous homomorphism to the abelian pro-`p` group `V^ab(p)`, so it factors through `G^ab(p)`. No
hypothesis on the cohomological dimension of `G` is needed. -/
theorem abelianizationProPTransfer_eq_one_of_mk_eq_one [CompactSpace G]
    [TotallyDisconnectedSpace G] (hV : IsOpen (V : Set G)) {g : G}
    (hg : maximalProPQuotient.mk p (TopologicalAbelianization G)
      (g : TopologicalAbelianization G) = 1) :
    abelianizationProPTransfer p G V g = 1 := by
  have : CompactSpace V := isCompact_iff_compactSpace.mp (V.isClosed_of_isOpen hV).isCompact
  let Ver : G →ₜ* abelianizationProP p G V :=
    ⟨abelianizationProPTransfer p G V, continuous_abelianizationProPTransfer p G V hV⟩
  let Verab := TopologicalAbelianization.lift Ver
  have hVer := congrArg (maximalProPQuotient.lift
    (isProP_maximalProPQuotient (p := p) (G := TopologicalAbelianization V)) Verab.toMonoidHom
    Verab.continuous) hg
  rw [maximalProPQuotient.mk_apply, maximalProPQuotient.lift_mk, map_one] at hVer
  exact (TopologicalAbelianization.lift_mk Ver g).symm.trans hVer

variable [V.Normal]

/-- On `V`, transfer is the norm of the conjugation action of `G ⧸ V`. -/
theorem abelianizationProPTransfer_apply_of_mem (v : V) :
    abelianizationProPTransfer p G V v =
      ∏ q : G ⧸ V, q • abelianizationProPMk p G V v := by
  rw [abelianizationProPTransfer, MonoidHom.transfer_eq_prod_mul_out]
  apply Finset.prod_congr rfl
  intro q _
  rw [← QuotientGroup.out_eq' q, abelianizationProPMk_conj]
  congr 1
  apply Subtype.ext
  simp [MulAut.conjNormal_apply, (QuotientGroup.eq_one_iff (v : G)).mpr v.property]

/-- At a quotient representative, transfer is the sum of the factor set in its first variable.
This is the additive form of the transfer formula used to evaluate the extension class. -/
theorem abelianizationProPTransfer_out (q : G ⧸ V) :
    Additive.ofMul (abelianizationProPTransfer p G V q.out) =
      ∑ r : G ⧸ V, abelianizationProPFactorSet p G V (r, q) := by
  rw [abelianizationProPTransfer, MonoidHom.transfer_eq_prod_mul_out]
  simp [abelianizationProPFactorSet_apply]

/-- The image of transfer is fixed by the conjugation action of `G ⧸ V`. This is a containment
in the invariants; equality with the invariants requires additional cohomological hypotheses. -/
@[simp]
theorem smul_abelianizationProPTransfer (q : G ⧸ V) (g : G) :
    q • abelianizationProPTransfer p G V g = abelianizationProPTransfer p G V g := by
  induction q using QuotientGroup.induction_on with
  | H a =>
    let φ := abelianizationProPMk p G V
    let ψ := (MulDistribMulAction.toMonoidHom (abelianizationProP p G V)
      (a : G ⧸ V)).comp φ
    have he : V.map (MulAut.conj a⁻¹).toMonoidHom = V :=
      Subgroup.Normal.map_conj_eq V a⁻¹
    have hφ : ∀ v : V,
        ψ ⟨(MulAut.conj a⁻¹).toMonoidHom v, by
          simpa only [he] using
            Subgroup.mem_map_of_mem (MulAut.conj a⁻¹).toMonoidHom v.property⟩ = φ v := by
      intro v
      simp only [ψ, MonoidHom.comp_apply, MulDistribMulAction.toMonoidHom_apply,
        φ, abelianizationProPMk_conj]
      congr 1
      apply Subtype.ext
      simp [MulAut.conjNormal_apply, mul_assoc]
    have h := MonoidHom.transfer_apply_of_mulEquiv φ (MulAut.conj a⁻¹) he ψ hφ g
    rw [MonoidHom.transfer_comp] at h
    -- Transfer has commutative target, so its value on the inner conjugate of `g` equals its
    -- value on `g`. Naturality then says that conjugation fixes the transferred value.
    simpa [φ, ψ, MonoidHom.comp_apply, MulAut.conj_apply, map_mul, map_inv,
      mul_comm, mul_left_comm, mul_assoc, abelianizationProPTransfer] using h

/-- Transfer from the whole group is the canonical map to its pro-`p` abelianization. -/
@[simp]
theorem abelianizationProPTransfer_top (g : G) :
    abelianizationProPTransfer p G ⊤ g =
      abelianizationProPMk p G ⊤ ⟨g, Subgroup.mem_top g⟩ := by
  have : Subsingleton (G ⧸ (⊤ : Subgroup G)) := QuotientGroup.subsingleton_quotient_top
  simpa only [Fintype.prod_subsingleton _ (1 : G ⧸ (⊤ : Subgroup G)), one_smul] using
    abelianizationProPTransfer_apply_of_mem p G ⊤ ⟨g, Subgroup.mem_top g⟩

end TauCeti
