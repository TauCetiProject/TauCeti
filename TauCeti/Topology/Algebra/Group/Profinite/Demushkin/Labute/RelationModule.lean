/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Group.TopologicalAbelianization
public import TauCeti.Topology.Algebra.Group.Profinite.CompletedGroupAlgebra.Map
public import TauCeti.Topology.Algebra.Group.Profinite.ProP.Relation.Module

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
  Additive (TopologicalAbelianization (χ : F →* ℤ_[p]ˣ).ker)

/-- The acting group `Γ = F / ker χ`, canonically isomorphic to the image of `χ`. -/
abbrev orientationQuotient (χ : F →ₜ* ℤ_[p]ˣ) : Type _ :=
  F ⧸ (χ : F →* ℤ_[p]ˣ).ker

/-- The action of `Γ` on `E` with Labute's inverse-conjugation convention. -/
noncomputable def labuteAction (χ : F →ₜ* ℤ_[p]ˣ) (γ : orientationQuotient χ)
    (x : labuteE χ) : labuteE χ :=
  Additive.ofMul (γ⁻¹ • Additive.toMul x)

omit [IsTopologicalGroup F] in
/-- The character quotient is commutative because it embeds into `ℤ_pˣ`. -/
theorem orientationQuotient_isMulCommutative (χ : F →ₜ* ℤ_[p]ˣ) :
    IsMulCommutative (orientationQuotient χ) :=
  Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr
    (Abelianization.commutator_subset_ker χ.toMonoidHom)

/-- Labute's conjugation gives an action by additive automorphisms. -/
private theorem labuteAction_laws (χ : F →ₜ* ℤ_[p]ˣ) (α β : orientationQuotient χ)
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

/-- The identity of the character quotient acts trivially. -/
@[simp]
theorem labuteAction_one (χ : F →ₜ* ℤ_[p]ˣ) (ξ : labuteE χ) :
    labuteAction χ 1 ξ = ξ :=
  (labuteAction_laws χ 1 1 ξ ξ).1

/-- The action respects multiplication in the character quotient. -/
@[simp]
theorem labuteAction_mul (χ : F →ₜ* ℤ_[p]ˣ) (α β : orientationQuotient χ)
    (ξ : labuteE χ) :
    labuteAction χ (α * β) ξ = labuteAction χ α (labuteAction χ β ξ) :=
  (labuteAction_laws χ α β ξ ξ).2.1

/-- Each element of the character quotient acts additively. -/
@[simp]
theorem labuteAction_add (χ : F →ₜ* ℤ_[p]ˣ) (α : orientationQuotient χ)
    (ξ η : labuteE χ) :
    labuteAction χ α (ξ + η) = labuteAction χ α ξ + labuteAction χ α η :=
  (labuteAction_laws χ α α ξ η).2.2

/-- The zero class is fixed by Labute's conjugation action. -/
@[simp]
theorem labuteAction_zero (χ : F →ₜ* ℤ_[p]ˣ) (γ : orientationQuotient χ) :
    labuteAction χ γ 0 = 0 := by
  simp [labuteAction]

/-- Labute's formula: the class of `y` sends the class of `x` to the class of `y⁻¹xy`. -/
@[simp]
theorem labuteAction_mk (χ : F →ₜ* ℤ_[p]ˣ) (y : F)
    (x : (χ : F →* ℤ_[p]ˣ).ker) :
    labuteAction χ (@QuotientGroup.mk F _ (χ : F →* ℤ_[p]ˣ).ker y)
      (Additive.ofMul (x : TopologicalAbelianization (χ : F →* ℤ_[p]ˣ).ker)) =
    Additive.ofMul
      ((⟨y⁻¹ * (x : F) * y,
        (inferInstance : (χ : F →* ℤ_[p]ˣ).ker.Normal).conj_mem' x x.2 y⟩ : (χ : F →* ℤ_[p]ˣ).ker) :
        TopologicalAbelianization (χ : F →* ℤ_[p]ˣ).ker) := by
  exact congrArg Additive.ofMul (TopologicalAbelianization.mk_inv_smul_mk _ y x)

/-- The inverse-conjugation action is jointly continuous. -/
theorem continuous_labuteAction (χ : F →ₜ* ℤ_[p]ˣ) :
    Continuous (fun z : orientationQuotient χ × labuteE χ =>
      labuteAction χ z.1 z.2) := by
  have h : Continuous (fun z : orientationQuotient χ × labuteE χ =>
      (Additive.toMul z.2 : TopologicalAbelianization (χ : F →* ℤ_[p]ˣ).ker)) := continuous_snd
  exact continuous_smul.comp ((continuous_inv.comp continuous_fst).prodMk h)

/-- The image of a relator in the abelianized character kernel. -/
noncomputable def labuteRelatorClass (χ : F →ₜ* ℤ_[p]ˣ) (r : F)
    (hr : r ∈ (χ : F →* ℤ_[p]ˣ).ker) :
    labuteE χ :=
  Additive.ofMul
    ((⟨r, hr⟩ : (χ : F →* ℤ_[p]ˣ).ker) : TopologicalAbelianization (χ : F →* ℤ_[p]ˣ).ker)

/-- Conjugating a relator before taking its class agrees with Labute's action. -/
@[simp]
theorem labuteAction_relatorClass (χ : F →ₜ* ℤ_[p]ˣ) (y r : F)
    (hr : r ∈ (χ : F →* ℤ_[p]ˣ).ker) :
    labuteAction χ (@QuotientGroup.mk F _ (χ : F →* ℤ_[p]ˣ).ker y)
      (labuteRelatorClass χ r hr) =
      labuteRelatorClass χ (y⁻¹ * r * y)
        ((inferInstance : (χ : F →* ℤ_[p]ˣ).ker.Normal).conj_mem' r hr y) :=
  labuteAction_mk χ y ⟨r, hr⟩

/-- Inclusion of the relation subgroup in the character kernel induces `R^{ab} → E`. -/
noncomputable def relationModuleToLabuteE (χ : F →ₜ* ℤ_[p]ˣ) (R : Subgroup F)
    (hR : R ≤ (χ : F →* ℤ_[p]ˣ).ker) :
    Additive (TopologicalAbelianization R) →+ labuteE χ :=
  (TopologicalAbelianization.map (Subgroup.inclusion hR)
    (Subgroup.continuous_inclusion hR)).toAdditive

/-- The map from the relation module takes a relator to its class in `E`. -/
@[simp]
theorem relationModuleToLabuteE_mk (χ : F →ₜ* ℤ_[p]ˣ) (R : Subgroup F)
    (hR : R ≤ (χ : F →* ℤ_[p]ˣ).ker) (r : R) :
    relationModuleToLabuteE χ R hR
      (Additive.ofMul (r : TopologicalAbelianization R)) =
      labuteRelatorClass χ r (hR r.2) := by
  -- Unwrap the additive homomorphism so `map_mk` applies to the multiplicative quotient.
  change Additive.ofMul
      (TopologicalAbelianization.map (Subgroup.inclusion hR)
        (Subgroup.continuous_inclusion hR) (r : TopologicalAbelianization R)) = _
  rw [TopologicalAbelianization.map_mk]
  -- The inclusion of `r : R` and its subtype representative in `ker χ` are definitionally equal.
  rfl

/-- The comparison map respects conjugation by a lift of an element of the character quotient. -/
@[simp]
theorem relationModuleToLabuteE_smul_mk (χ : F →ₜ* ℤ_[p]ˣ) (R : Subgroup F)
    [R.Normal] (hR : R ≤ (χ : F →* ℤ_[p]ˣ).ker) (y : F)
    (x : Additive (TopologicalAbelianization R)) :
    relationModuleToLabuteE χ R hR
      ((y : F ⧸ R)⁻¹ • x) =
      labuteAction χ (QuotientGroup.mk y) (relationModuleToLabuteE χ R hR x) := by
  exact congrArg Additive.ofMul
    (TopologicalAbelianization.map_inclusion_mk_smul hR y⁻¹ (Additive.toMul x))

section CompletedAction

variable [CompactSpace F] [TotallyDisconnectedSpace F]

open scoped IsMulCommutative

/-- The `ℤ_p[[Γ]]`-action on Labute's `E`, obtained by applying inversion to the group algebra
and then using the completed conjugation action. -/
noncomputable def labuteSMul (hF : IsProP p F) (χ : F →ₜ* ℤ_[p]ˣ)
    (a : completedGroupAlgebra ℤ_[p] (orientationQuotient χ)) (ξ : labuteE χ) :
    labuteE χ := by
  letI : CommGroup (orientationQuotient χ) := by
    letI : IsMulCommutative (orientationQuotient χ) := orientationQuotient_isMulCommutative χ
    infer_instance
  have h_inv : Continuous (invMonoidHom : orientationQuotient χ → orientationQuotient χ) := by
    simpa only [coe_invMonoidHom] using
      (continuous_inv : Continuous (fun γ : orientationQuotient χ => γ⁻¹))
  letI : IsClosed ((χ : F →* ℤ_[p]ˣ).ker : Set F) :=
    χ.coe_ker ▸ isClosed_singleton.preimage χ.continuous
  letI := (hF.topologicalAbelianization (χ : F →* ℤ_[p]ˣ).ker).completedGroupAlgebraModule
    (orientationQuotient χ)
  exact completedGroupAlgebra.map ℤ_[p] invMonoidHom h_inv a • ξ

/-- Labute's completed action as a module over `ℤ_p[[Γ]]`. -/
@[instance_reducible]
noncomputable def labuteModule (hF : IsProP p F) (χ : F →ₜ* ℤ_[p]ˣ) :
    Module (completedGroupAlgebra ℤ_[p] (orientationQuotient χ)) (labuteE χ) := by
  letI : CommGroup (orientationQuotient χ) := by
    letI : IsMulCommutative (orientationQuotient χ) := orientationQuotient_isMulCommutative χ
    infer_instance
  have h_inv : Continuous (invMonoidHom : orientationQuotient χ → orientationQuotient χ) := by
    simpa only [coe_invMonoidHom] using
      (continuous_inv : Continuous (fun γ : orientationQuotient χ => γ⁻¹))
  letI : IsClosed ((χ : F →* ℤ_[p]ˣ).ker : Set F) :=
    χ.coe_ker ▸ isClosed_singleton.preimage χ.continuous
  letI := (hF.topologicalAbelianization (χ : F →* ℤ_[p]ˣ).ker).completedGroupAlgebraModule
    (orientationQuotient χ)
  exact Module.compHom (labuteE χ)
    (completedGroupAlgebra.map ℤ_[p] invMonoidHom h_inv).toRingHom

/-- The scalar multiplication in `labuteModule` is Labute's twisted action. -/
@[simp]
theorem labuteModule_smul (hF : IsProP p F) (χ : F →ₜ* ℤ_[p]ˣ)
    (a : completedGroupAlgebra ℤ_[p] (orientationQuotient χ)) (ξ : labuteE χ) :
    letI := labuteModule hF χ
    a • ξ = labuteSMul hF χ a ξ := by
  -- Both sides use the same `Module.compHom` action; this exposes its `smul` field.
  change (labuteModule hF χ).smul a ξ = labuteSMul hF χ a ξ
  rfl

/-- The completed action extends inverse conjugation by group elements. -/
@[simp]
theorem labuteSMul_of (hF : IsProP p F) (χ : F →ₜ* ℤ_[p]ˣ)
    (γ : orientationQuotient χ) (ξ : labuteE χ) :
    labuteSMul hF χ (completedGroupAlgebra.of ℤ_[p] (orientationQuotient χ) γ) ξ =
      labuteAction χ γ ξ := by
  let _ : CommGroup (orientationQuotient χ) := by
    letI : IsMulCommutative (orientationQuotient χ) := orientationQuotient_isMulCommutative χ
    infer_instance
  let _ : IsClosed ((χ : F →* ℤ_[p]ˣ).ker : Set F) :=
    χ.coe_ker ▸ isClosed_singleton.preimage χ.continuous
  let _ := (hF.topologicalAbelianization (χ : F →* ℤ_[p]ˣ).ker).completedGroupAlgebraModule
    (orientationQuotient χ)
  rw [labuteSMul, completedGroupAlgebra.map_of]
  exact (hF.topologicalAbelianization (χ : F →* ℤ_[p]ˣ).ker).completedGroupAlgebraModule_of_smul
    (invMonoidHom γ) ξ

/-- The completed action satisfies the unit, multiplication and additivity laws of a module. -/
theorem labuteSMul_laws (hF : IsProP p F) (χ : F →ₜ* ℤ_[p]ˣ)
    (a b : completedGroupAlgebra ℤ_[p] (orientationQuotient χ)) (ξ η : labuteE χ) :
    labuteSMul hF χ 1 ξ = ξ ∧
      labuteSMul hF χ (a * b) ξ = labuteSMul hF χ a (labuteSMul hF χ b ξ) ∧
      labuteSMul hF χ (a + b) ξ = labuteSMul hF χ a ξ + labuteSMul hF χ b ξ ∧
      labuteSMul hF χ a (ξ + η) = labuteSMul hF χ a ξ + labuteSMul hF χ a η := by
  let _ : CommGroup (orientationQuotient χ) := by
    letI : IsMulCommutative (orientationQuotient χ) := orientationQuotient_isMulCommutative χ
    infer_instance
  let _ : IsClosed ((χ : F →* ℤ_[p]ˣ).ker : Set F) :=
    χ.coe_ker ▸ isClosed_singleton.preimage χ.continuous
  let _ := (hF.topologicalAbelianization (χ : F →* ℤ_[p]ˣ).ker).completedGroupAlgebraModule
    (orientationQuotient χ)
  simp [labuteSMul, mul_smul, add_smul, smul_add]

/-- The unit of the completed group algebra acts trivially. -/
@[simp]
theorem labuteSMul_one (hF : IsProP p F) (χ : F →ₜ* ℤ_[p]ˣ) (ξ : labuteE χ) :
    labuteSMul hF χ 1 ξ = ξ :=
  (labuteSMul_laws hF χ 1 1 ξ ξ).1

/-- The completed action respects multiplication of scalars. -/
@[simp]
theorem labuteSMul_mul (hF : IsProP p F) (χ : F →ₜ* ℤ_[p]ˣ)
    (a b : completedGroupAlgebra ℤ_[p] (orientationQuotient χ)) (ξ : labuteE χ) :
    labuteSMul hF χ (a * b) ξ = labuteSMul hF χ a (labuteSMul hF χ b ξ) :=
  (labuteSMul_laws hF χ a b ξ ξ).2.1

/-- The completed action respects addition of scalars. -/
@[simp]
theorem labuteSMul_add (hF : IsProP p F) (χ : F →ₜ* ℤ_[p]ˣ)
    (a b : completedGroupAlgebra ℤ_[p] (orientationQuotient χ)) (ξ : labuteE χ) :
    labuteSMul hF χ (a + b) ξ = labuteSMul hF χ a ξ + labuteSMul hF χ b ξ :=
  (labuteSMul_laws hF χ a b ξ ξ).2.2.1

/-- Every completed scalar acts additively on Labute's module. -/
@[simp]
theorem labuteSMul_add_right (hF : IsProP p F) (χ : F →ₜ* ℤ_[p]ˣ)
    (a : completedGroupAlgebra ℤ_[p] (orientationQuotient χ)) (ξ η : labuteE χ) :
    labuteSMul hF χ a (ξ + η) = labuteSMul hF χ a ξ + labuteSMul hF χ a η :=
  (labuteSMul_laws hF χ a a ξ η).2.2.2

/-- Zero in the completed group algebra acts trivially. -/
@[simp]
theorem labuteSMul_zero (hF : IsProP p F) (χ : F →ₜ* ℤ_[p]ˣ) (ξ : labuteE χ) :
    labuteSMul hF χ 0 ξ = 0 := by
  let _ := labuteModule hF χ
  rw [← labuteModule_smul]
  exact zero_smul _ ξ

/-- Every completed scalar sends the zero class to zero. -/
@[simp]
theorem labuteSMul_zero_right (hF : IsProP p F) (χ : F →ₜ* ℤ_[p]ˣ)
    (a : completedGroupAlgebra ℤ_[p] (orientationQuotient χ)) :
    labuteSMul hF χ a 0 = 0 := by
  let _ := labuteModule hF χ
  rw [← labuteModule_smul]
  exact smul_zero a

/-- The completed action on Labute's module is jointly continuous. -/
theorem continuous_labuteSMul (hF : IsProP p F) (χ : F →ₜ* ℤ_[p]ˣ) :
    Continuous (fun z : completedGroupAlgebra ℤ_[p] (orientationQuotient χ) × labuteE χ =>
      labuteSMul hF χ z.1 z.2) := by
  let _ : CommGroup (orientationQuotient χ) := by
    letI : IsMulCommutative (orientationQuotient χ) := orientationQuotient_isMulCommutative χ
    infer_instance
  have h_inv : Continuous (invMonoidHom : orientationQuotient χ → orientationQuotient χ) := by
    simpa only [coe_invMonoidHom] using
      (continuous_inv : Continuous (fun γ : orientationQuotient χ => γ⁻¹))
  let _ : IsClosed ((χ : F →* ℤ_[p]ˣ).ker : Set F) :=
    χ.coe_ker ▸ isClosed_singleton.preimage χ.continuous
  let _ := (hF.topologicalAbelianization (χ : F →* ℤ_[p]ˣ).ker).completedGroupAlgebraModule
    (orientationQuotient χ)
  let _ :=
    (hF.topologicalAbelianization (χ : F →* ℤ_[p]ˣ).ker).continuousSMul_completedGroupAlgebraModule
      (orientationQuotient χ)
  exact continuous_smul.comp
    (((completedGroupAlgebra.continuous_map ℤ_[p]
      (invMonoidHom : orientationQuotient χ →* orientationQuotient χ)
      h_inv).comp continuous_fst).prodMk continuous_snd)

end CompletedAction

end TauCeti
