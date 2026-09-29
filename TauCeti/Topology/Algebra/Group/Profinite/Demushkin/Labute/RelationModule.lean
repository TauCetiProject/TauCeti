/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Group.TopologicalAbelianization
public import TauCeti.Topology.Algebra.Group.Profinite.CompletedGroupAlgebra.Map
public import TauCeti.Topology.Algebra.Group.Profinite.ProP.RelationModule

/-!
# Labute's abelianized character kernel

For a character `χ : F → ℤ_pˣ` on the free group of a pro-`p` presentation, Labute's module is
the topological abelianization `E` of `ker χ`. It is not the abelianization of the relation
subgroup. The relation subgroup maps to `E`, and a relator has a distinguished class there.
The quotient `F ⧸ ker χ` acts on `E` by conjugation. We use Labute's convention in which the
class of `y` acts on the class of `x` by the class of `y⁻¹xy`.

The generic conjugation action and the induced map on topological abelianizations are supplied
by `TauCeti.Topology.Algebra.Group.TopologicalAbelianization`. The resulting objects are the
ones used in Labute's computation of Demushkin relators (Labute, §4, p. 121).

The `ℤ_p[[Γ]]`-action is obtained from the existing completed conjugation module by the
continuous algebra automorphism induced by inversion on the commutative group `Γ`. This keeps
Labute's inverse-conjugation convention without changing the underlying abelian group of `E`.

## References

* J. P. Labute, *Classification of Demushkin groups*, Canad. J. Math. 19 (1967), §4.
-/

public section

namespace TauCeti

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Group F] [TopologicalSpace F]
  [IsTopologicalGroup F]

/-- Labute's `E = X/(X,X)` for `X = ker χ`, written additively. -/
abbrev labuteE (χ : F →ₜ* ℤ_[p]ˣ) : Type _ :=
  Additive (TopologicalAbelianization χ.toMonoidHom.ker)

/-- The acting group `Γ = F / ker χ`, canonically isomorphic to the image of `χ`. -/
abbrev orientationQuotient (χ : F →ₜ* ℤ_[p]ˣ) : Type _ :=
  F ⧸ χ.toMonoidHom.ker

/-- Labute's `E` is abelian. -/
theorem labuteE_add_comm (χ : F →ₜ* ℤ_[p]ˣ) (x y : labuteE χ) : x + y = y + x :=
  add_comm x y

/-- The action of `Γ` on `E` with Labute's inverse-conjugation convention. -/
noncomputable def labuteAction (χ : F →ₜ* ℤ_[p]ˣ) (γ : orientationQuotient χ)
    (x : labuteE χ) : labuteE χ :=
  Additive.ofMul (γ⁻¹ • Additive.toMul x)

omit [IsTopologicalGroup F] in
/-- The character quotient is commutative because it embeds into `ℤ_pˣ`. -/
private theorem orientationQuotient_isMulCommutative (χ : F →ₜ* ℤ_[p]ˣ) :
    IsMulCommutative (orientationQuotient χ) :=
  Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr
    (Abelianization.commutator_subset_ker χ.toMonoidHom)

/-- Labute's conjugation gives an action by additive automorphisms. -/
theorem labuteAction_laws (χ : F →ₜ* ℤ_[p]ˣ) (α β : orientationQuotient χ)
    (ξ η : labuteE χ) :
    labuteAction χ 1 ξ = ξ ∧
      labuteAction χ (α * β) ξ = labuteAction χ α (labuteAction χ β ξ) ∧
      labuteAction χ α (ξ + η) = labuteAction χ α ξ + labuteAction χ α η := by
  have hcomm : α * β = β * α := by
    exact isMulCommutative_iff.mp (orientationQuotient_isMulCommutative χ) α β
  constructor
  · simp [labuteAction]
  constructor
  · simp only [labuteAction, hcomm, mul_inv_rev, mul_smul, toMul_ofMul]
  · simp only [labuteAction, toMul_add, smul_mul', ofMul_mul]

/-- Labute's formula: the class of `y` sends the class of `x` to the class of `y⁻¹xy`. -/
@[simp]
theorem labuteAction_mk (χ : F →ₜ* ℤ_[p]ˣ) (y : F) (x : χ.toMonoidHom.ker) :
    labuteAction χ (QuotientGroup.mk y)
      (Additive.ofMul (x : TopologicalAbelianization χ.toMonoidHom.ker)) =
    Additive.ofMul
      ((⟨y⁻¹ * (x : F) * y,
        (inferInstance : χ.toMonoidHom.ker.Normal).conj_mem' x x.2 y⟩ : χ.toMonoidHom.ker) :
        TopologicalAbelianization χ.toMonoidHom.ker) := by
  exact congrArg Additive.ofMul (TopologicalAbelianization.mk_inv_smul_mk _ y x)

/-- The inverse-conjugation action is jointly continuous. -/
theorem continuous_labuteAction (χ : F →ₜ* ℤ_[p]ˣ) :
    Continuous (fun z : orientationQuotient χ × labuteE χ =>
      labuteAction χ z.1 z.2) := by
  have h : Continuous (fun z : orientationQuotient χ × labuteE χ =>
      (Additive.toMul z.2 : TopologicalAbelianization χ.toMonoidHom.ker)) := continuous_snd
  exact continuous_smul.comp ((continuous_inv.comp continuous_fst).prodMk h)

/-- The image of a relator in the abelianized character kernel. -/
noncomputable def labuteRelatorClass (χ : F →ₜ* ℤ_[p]ˣ) (r : F) (hr : r ∈ χ.toMonoidHom.ker) :
    labuteE χ :=
  Additive.ofMul ((⟨r, hr⟩ : χ.toMonoidHom.ker) : TopologicalAbelianization χ.toMonoidHom.ker)

/-- Conjugating a relator before taking its class agrees with Labute's action. -/
@[simp]
theorem labuteAction_relatorClass (χ : F →ₜ* ℤ_[p]ˣ) (y r : F)
    (hr : r ∈ χ.toMonoidHom.ker) :
    labuteAction χ (QuotientGroup.mk y) (labuteRelatorClass χ r hr) =
      labuteRelatorClass χ (y⁻¹ * r * y)
        ((inferInstance : χ.toMonoidHom.ker.Normal).conj_mem' r hr y) :=
  labuteAction_mk χ y ⟨r, hr⟩

/-- Inclusion of the relation subgroup in the character kernel induces `R^{ab} → E`. -/
noncomputable def relationModuleToLabuteE (χ : F →ₜ* ℤ_[p]ˣ) (R : Subgroup F) [R.Normal]
    (hR : R ≤ χ.toMonoidHom.ker) :
    Additive (TopologicalAbelianization R) →+ labuteE χ :=
  (TopologicalAbelianization.map (Subgroup.inclusion hR)
    (Subgroup.continuous_inclusion hR)).toAdditive

/-- The map from the relation module takes a relator to its class in `E`. -/
@[simp]
theorem relationModuleToLabuteE_mk (χ : F →ₜ* ℤ_[p]ˣ) (R : Subgroup F) [R.Normal]
    (hR : R ≤ χ.toMonoidHom.ker) (r : R) :
    relationModuleToLabuteE χ R hR
      (Additive.ofMul (r : TopologicalAbelianization R)) =
      labuteRelatorClass χ r (hR r.2) := by
  simp [relationModuleToLabuteE, labuteRelatorClass]
  rfl

/-- The comparison map respects conjugation by a lift of an element of the character quotient. -/
theorem relationModuleToLabuteE_smul_mk (χ : F →ₜ* ℤ_[p]ˣ) (R : Subgroup F)
    [R.Normal] (hR : R ≤ χ.toMonoidHom.ker) (y : F)
    (x : Additive (TopologicalAbelianization R)) :
    relationModuleToLabuteE χ R hR
      (Additive.ofMul ((y : F ⧸ R)⁻¹ • Additive.toMul x)) =
      labuteAction χ (QuotientGroup.mk y) (relationModuleToLabuteE χ R hR x) := by
  exact congrArg Additive.ofMul
    (TopologicalAbelianization.map_inclusion_mk_smul hR y⁻¹ (Additive.toMul x))

section CompletedAction

variable [CompactSpace F] [TotallyDisconnectedSpace F]

/-- Inversion on the commutative character quotient. This switches Mathlib's conjugation
convention to Labute's inverse-conjugation convention. -/
private noncomputable def orientationQuotientInv (χ : F →ₜ* ℤ_[p]ˣ) :
    orientationQuotient χ →* orientationQuotient χ where
  toFun := Inv.inv
  map_one' := inv_one
  map_mul' a b := by
    rw [mul_inv_rev]
    exact (isMulCommutative_iff.mp (orientationQuotient_isMulCommutative χ) b⁻¹ a⁻¹)

omit [CompactSpace F] [TotallyDisconnectedSpace F] in
/-- Inversion is continuous on the character quotient. -/
private theorem continuous_orientationQuotientInv (χ : F →ₜ* ℤ_[p]ˣ) :
    Continuous (orientationQuotientInv χ) :=
  continuous_inv

/-- The `ℤ_p[[Γ]]`-action on Labute's `E`, obtained by applying inversion to the group algebra
and then using the completed conjugation action. -/
noncomputable def labuteSMul (hF : IsProP p F) (χ : F →ₜ* ℤ_[p]ˣ)
    (a : completedGroupAlgebra ℤ_[p] (orientationQuotient χ)) (ξ : labuteE χ) :
    labuteE χ := by
  letI : IsClosed (χ.toMonoidHom.ker : Set F) :=
    χ.coe_ker ▸ isClosed_singleton.preimage χ.continuous
  letI := (hF.topologicalAbelianization χ.toMonoidHom.ker).completedGroupAlgebraModule
    (orientationQuotient χ)
  exact completedGroupAlgebra.map ℤ_[p] (orientationQuotientInv χ)
    (continuous_orientationQuotientInv χ) a • ξ

/-- The completed action extends inverse conjugation by group elements. -/
theorem labuteSMul_of (hF : IsProP p F) (χ : F →ₜ* ℤ_[p]ˣ)
    (γ : orientationQuotient χ) (ξ : labuteE χ) :
    labuteSMul hF χ (completedGroupAlgebra.of ℤ_[p] (orientationQuotient χ) γ) ξ =
      labuteAction χ γ ξ := by
  let _ : IsClosed (χ.toMonoidHom.ker : Set F) :=
    χ.coe_ker ▸ isClosed_singleton.preimage χ.continuous
  let _ := (hF.topologicalAbelianization χ.toMonoidHom.ker).completedGroupAlgebraModule
    (orientationQuotient χ)
  rw [labuteSMul, completedGroupAlgebra.map_of]
  exact (hF.topologicalAbelianization χ.toMonoidHom.ker).completedGroupAlgebraModule_of_smul
    (orientationQuotientInv χ γ) ξ

/-- The completed action satisfies the unit, multiplication and additivity laws of a module. -/
theorem labuteSMul_laws (hF : IsProP p F) (χ : F →ₜ* ℤ_[p]ˣ)
    (a b : completedGroupAlgebra ℤ_[p] (orientationQuotient χ)) (ξ η : labuteE χ) :
    labuteSMul hF χ 1 ξ = ξ ∧
      labuteSMul hF χ (a * b) ξ = labuteSMul hF χ a (labuteSMul hF χ b ξ) ∧
      labuteSMul hF χ (a + b) ξ = labuteSMul hF χ a ξ + labuteSMul hF χ b ξ ∧
      labuteSMul hF χ a (ξ + η) = labuteSMul hF χ a ξ + labuteSMul hF χ a η := by
  let _ : IsClosed (χ.toMonoidHom.ker : Set F) :=
    χ.coe_ker ▸ isClosed_singleton.preimage χ.continuous
  let _ := (hF.topologicalAbelianization χ.toMonoidHom.ker).completedGroupAlgebraModule
    (orientationQuotient χ)
  simp [labuteSMul, mul_smul, add_smul, smul_add]

/-- The completed action on Labute's module is jointly continuous. -/
theorem continuous_labuteSMul (hF : IsProP p F) (χ : F →ₜ* ℤ_[p]ˣ) :
    Continuous (fun z : completedGroupAlgebra ℤ_[p] (orientationQuotient χ) × labuteE χ =>
      labuteSMul hF χ z.1 z.2) := by
  let _ : IsClosed (χ.toMonoidHom.ker : Set F) :=
    χ.coe_ker ▸ isClosed_singleton.preimage χ.continuous
  let _ := (hF.topologicalAbelianization χ.toMonoidHom.ker).completedGroupAlgebraModule
    (orientationQuotient χ)
  let _ :=
    (hF.topologicalAbelianization χ.toMonoidHom.ker).continuousSMul_completedGroupAlgebraModule
      (orientationQuotient χ)
  exact continuous_smul.comp
    (((completedGroupAlgebra.continuous_map ℤ_[p] (orientationQuotientInv χ)
      (continuous_orientationQuotientInv χ)).comp continuous_fst).prodMk continuous_snd)

end CompletedAction

end TauCeti
