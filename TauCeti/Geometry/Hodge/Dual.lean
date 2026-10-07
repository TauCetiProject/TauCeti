/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dual.Lemmas
public import TauCeti.Geometry.Hodge.WeilOperator

/-!
# The dual of a pure Hodge structure

The dual `V^*` of a pure Hodge structure of weight `n` is a pure Hodge structure of weight `-n`
on the complex dual space: its filtration step at index `p` is the annihilator of the filtration
step of index `1 - p` of the original structure, and its conjugation is the twisted transpose of
the original conjugation, sending a functional `φ` to `v ↦ conj (φ (ω v))`.
The dual pairing then respects Hodge components of complementary indices: the `p`-th component
of the dual pairs nontrivially only against the component of index `-p`, and, when `W` is
finite-dimensional, has the same dimension as the `(-p)`-th component, so dualizing reflects
the table of Hodge numbers. The pairing is invariant under the Weil operators, so the Weil
operator of the dual is the transpose of the inverse Weil operator.

For an integral pure Hodge structure the dual is carried by the dual lattice `Hom_ℤ(V, ℤ)`: the
complex dual of the complexification is a complexification of the dual lattice, whose lattice
conjugation is the twisted transpose (`TauCeti.Hodge.latticeConjugation_dual`). Dualizing is
contravariantly functorial in morphisms, at both the complex and the integral level.

This is the dual companion to tensor products of pure Hodge structures, following Deligne,
*Théorie de Hodge II*, §2.1, and Peters–Steenbrink, *Mixed Hodge Structures*, §2.1; the internal
Hom of two pure Hodge structures is the tensor product of the dual of the source with the target.

## Main declarations

* `TauCeti.Hodge.HodgeStructureOn.dual`: the dual pure Hodge structure, of weight `-n`; its
  conjugation is the twisted transpose `TauCeti.Hodge.Conjugation.dual`, and the opposedness of
  its filtration holds since dual annihilators carry complements to complements.
* `TauCeti.Hodge.HodgeStructureOn.dual_F`, `…dual_conjF`: the step of the dual filtration at
  index `p` is the annihilator of the original step `1 - p`, and the conjugate step is the
  annihilator of the original conjugate step `1 - p`.
* `TauCeti.Hodge.HodgeStructureOn.dual_piece`: the components of the dual structure are
  annihilators of sums of complementary filtration steps.
* `TauCeti.Hodge.HodgeStructureOn.finrank_dual_piece`: when `W` is finite-dimensional, the
  dimension of the `p`-th component of the dual equals that of the `(-p)`-th component.
* `TauCeti.Hodge.HodgeStructureOn.apply_eq_zero_of_mem_piece_of_ne`: the dual pairing vanishes
  between components unless their indices are complementary.
* `TauCeti.Hodge.HodgeStructureOn.weilOperator_dual`: the Weil operator of the dual is the
  transpose of the inverse Weil operator, so that the dual pairing is Weil-invariant
  (`TauCeti.Hodge.HodgeStructureOn.weilOperator_dual_apply_weilOperator`).
* `TauCeti.Hodge.HodgeStructureOn.IsMorphism.dualMap`: the transpose of a morphism of pure Hodge
  structures is a morphism between the duals.
* `TauCeti.Hodge.HodgeStructure.dual`: the dual of an integral pure Hodge structure, on the dual
  lattice, with `TauCeti.Hodge.HodgeStructure.dual_F`, `…dual_piece` and `…dual_weilOperator`
  identifying its filtration, components and Weil operator with those of the complex dual.
* `TauCeti.Hodge.HodgeStructure.Hom.dualMap`: the transpose of a morphism of integral pure Hodge
  structures, with `TauCeti.Hodge.HodgeStructure.Hom.dualMap_id` and `…dualMap_comp` its
  contravariant functoriality.
-/

public section

namespace TauCeti.Hodge

universe u

variable {W : Type u} [AddCommGroup W] [Module ℂ W]

namespace HodgeStructureOn

variable {ω : Conjugation W} {n : ℤ}

/-- Opposedness of the dual filtration: the annihilators of a complementary pair are
complementary. -/
private theorem isCompl_dual_annihilator (hs : HodgeStructureOn W ω n) (p : ℤ) :
    IsCompl (hs.F (1 - p)).dualAnnihilator
      ((hs.F (1 - (-n + 1 - p))).dualAnnihilator.map
        ω.dual.toEquiv.toLinearMap) := by
  have hidx : 1 - (-n + 1 - p) = n + p := by ring
  have hkey : n + 1 - (1 - p) = n + p := by ring
  have key := hs.isCompl_F_conjF (1 - p)
  rw [hkey] at key
  rw [hidx, Conjugation.map_dualAnnihilator, ← hs.conjF_def]
  exact Subspace.isCompl_dualAnnihilator key

variable (hs : HodgeStructureOn W ω n)

/-- **The dual pure Hodge structure**, of weight `-n`.

Its filtration step at index `p` is the annihilator of the original filtration step of index
`1 - p`; its conjugation is the twisted transpose `TauCeti.Hodge.Conjugation.dual`. Opposedness
of the dual filtration rests on the fact that dual annihilators carry complements to
complements (`Subspace.isCompl_dualAnnihilator`). -/
noncomputable def dual :
    HodgeStructureOn (Module.Dual ℂ W) ω.dual (-n) where
  F p := (hs.F (1 - p)).dualAnnihilator
  F_antitone := fun p q hpq =>
    Submodule.dualAnnihilator_anti (hs.F_antitone (by omega))
  F_top := by
    obtain ⟨q, hq⟩ := hs.F_bot
    refine ⟨1 - q, ?_⟩
    have hq' : 1 - (1 - q) = q := by ring
    rw [hq', hq, Submodule.dualAnnihilator_bot]
  opposed := hs.isCompl_dual_annihilator

/-- The filtration of the dual Hodge structure is made of dual annihilators of steps. -/
@[simp]
theorem dual_F (p : ℤ) :
    (hs.dual).F p = (hs.F (1 - p)).dualAnnihilator :=
  (rfl)

/-- The conjugate of a step of the dual filtration is the annihilator of a conjugate step. -/
@[simp]
theorem dual_conjF (p : ℤ) :
    (hs.dual).conjF p = (hs.conjF (1 - p)).dualAnnihilator := by
  rw [(hs.dual).conjF_def, hs.dual_F, Conjugation.map_dualAnnihilator, ← hs.conjF_def]

/-- A component of the dual Hodge structure is the annihilator of the sum of the two filtration
steps flanking the component of complementary index. -/
@[simp]
theorem dual_piece (p : ℤ) :
    (hs.dual).piece p =
      ((hs.F (1 - p)) ⊔ (hs.conjF (n + 1 + p))).dualAnnihilator := by
  rw [piece_def, hs.dual_F, dual_conjF, ← Submodule.dualAnnihilator_sup_eq]
  have hidx : 1 - (-n - p) = n + 1 + p := by omega
  rw [hidx]

section Dimension

/-- If `B` complements a submodule `C ≤ A`, the part of `A` complementary to `B` together with
`C` fills `A`. -/
private theorem finrank_inf_add_finrank_eq_finrank {A B C : Submodule ℂ W}
    (hcompl : IsCompl C B) (hCA : C ≤ A) [Module.Finite ℂ W] :
    Module.finrank ℂ ↥(A ⊓ B) + Module.finrank ℂ ↥C = Module.finrank ℂ ↥A := by
  have hsup : C ⊔ A ⊓ B = A := by
    refine le_antisymm (sup_le hCA inf_le_left) ?_
    intro x hxA
    have hx' : x ∈ (C ⊔ B : Submodule ℂ W) :=
      (le_of_eq hcompl.codisjoint.eq_top.symm) Submodule.mem_top
    obtain ⟨c, hc, b, hb, hx⟩ := Submodule.mem_sup.1 hx'
    have hm : x - c ∈ A := sub_mem hxA (hCA hc)
    have hxcb : x - c = b := by rw [← hx]; abel
    have hbx : x - c ∈ B := by rw [hxcb]; exact hb
    exact Submodule.mem_sup.mpr ⟨c, hc, x - c, ⟨hm, hbx⟩,
      by rw [hxcb]; exact hx⟩
  have hdisj : Disjoint C (A ⊓ B) :=
    hcompl.disjoint.mono_right inf_le_right
  have key := Submodule.finrank_sup_add_finrank_inf_eq C (A ⊓ B)
  rw [disjoint_iff.mp hdisj, finrank_bot, add_zero, hsup] at key
  omega

/-- The dimension of the `p`-th component of the dual Hodge structure equals the dimension of
the `(-p)`-th component: dualizing reflects the table of Hodge numbers. -/
theorem finrank_dual_piece [Module.Finite ℂ W] (p : ℤ) :
    Module.finrank ℂ ((hs.dual).piece p) = Module.finrank ℂ (hs.piece (-p)) := by
  have hnpp : n - -p = n + p := by ring
  have hidx1 : n + 1 - (1 - p) = n + p := by ring
  have hidx2 : n + 1 - -p = n + 1 + p := by ring
  have hle : n + p ≤ n + 1 + p := by omega
  rw [dual_piece, piece_def, hnpp, inf_comm]
  have hcomp1 := hs.isCompl_F_conjF (1 - p)
  rw [hidx1] at hcomp1
  have hcomp2 := hs.isCompl_F_conjF (-p)
  rw [hidx2] at hcomp2
  have hd : Disjoint (hs.F (1 - p)) (hs.conjF (n + 1 + p)) :=
    hcomp1.disjoint.mono_right (hs.conjF_antitone hle)
  have hL1 := Subspace.finrank_add_finrank_dualAnnihilator_eq
    ((hs.F (1 - p)) ⊔ (hs.conjF (n + 1 + p)))
  have hsup := Submodule.finrank_sup_add_finrank_inf_eq (hs.F (1 - p)) (hs.conjF (n + 1 + p))
  rw [hd.eq_bot, finrank_bot, add_zero] at hsup
  have hsum := Submodule.finrank_add_eq_of_isCompl hcomp1
  have hrhs := finrank_inf_add_finrank_eq_finrank hcomp2.symm (hs.conjF_antitone hle)
  omega

end Dimension

/-- A functional in the `p`-th component of the dual vanishes on every component whose index is
not `-p`: the dual pairing pairs the `p`-th component of the dual only against the component of
complementary index. -/
theorem apply_eq_zero_of_mem_piece_of_ne {a p : ℤ}
    {u : W} {φ : Module.Dual ℂ W} (hu : u ∈ hs.piece a) (hφ : φ ∈ (hs.dual).piece p)
    (hne : a ≠ -p) :
    φ u = 0 := by
  simp only [dual_piece, Submodule.mem_dualAnnihilator] at hφ
  have hpair := (mem_piece_iff hs a u).mp hu
  rcases lt_trichotomy a (-p) with hlt | heq | hgt
  · have hlt' : n + 1 + p ≤ n - a := by omega
    exact hφ u (Submodule.mem_sup_right (hs.conjF_antitone hlt' hpair.2))
  · exact absurd heq hne
  · have hle : 1 - p ≤ a := by omega
    exact hφ u (Submodule.mem_sup_left (hs.F_antitone hle hpair.1))

section WeilOperator

/-- The scalar by which the inverse Weil operator acts on the component of index `-p` and weight
`n` is the scalar by which the Weil operator of the dual acts on the component of index `p` and
weight `-n`: `(-1)^n i^{-2p-n} = i^{2p+n}` since `i^4 = 1`. -/
private theorem neg_one_zpow_mul_I_zpow (n p : ℤ) :
    (-1 : ℂ) ^ n * Complex.I ^ (2 * -p - n) = Complex.I ^ (2 * p + n) := by
  -- Split the exponent on the right as `2p + n = 2n + (2(-p) - n) + 4p`: the summand `2(-p) - n`
  -- matches the left-hand exponent, and the two remaining factors `i^(2n) = (i^2)^n = (-1)^n` and
  -- `i^(4p) = (i^4)^p = 1` are closed by `simp` once `zpow_mul` peels off the exponents `2`, `4`.
  rw [show (2 : ℤ) * p + n = 2 * n + (2 * -p - n) + 4 * p by ring, zpow_add₀ Complex.I_ne_zero,
    zpow_add₀ Complex.I_ne_zero, zpow_mul, zpow_mul]
  simp

/-- **The Weil operator of the dual is the transpose of the inverse Weil operator.** On the
`p`-th component of the dual, of weight `-n`, it acts by `i^{2p+n}`, and that is the inverse of
the scalar `i^{-2p-n}` by which the Weil operator acts on the complementary component of index
`-p`. -/
@[simp]
theorem weilOperator_dual :
    hs.dual.weilOperator = hs.weilOperatorEquiv.symm.toLinearMap.dualMap := by
  refine (hs.dual.weilOperator_unique _ fun p φ hφ ↦ ?_).symm
  refine hs.linearMap_ext_of_piece fun a x hx ↦ ?_
  simp only [LinearMap.dualMap_apply, LinearEquiv.coe_coe, weilOperatorEquiv_symm_apply,
    hs.weilOperator_apply_of_mem hx, LinearMap.smul_apply, map_smul, smul_eq_mul, sub_neg_eq_add]
  by_cases ha : a = -p
  · subst ha
    rw [← mul_assoc, neg_one_zpow_mul_I_zpow]
  · simp [hs.apply_eq_zero_of_mem_piece_of_ne hx hφ ha]

/-- **The dual pairing is Weil-invariant:** `⟨C φ, C x⟩ = ⟨φ, x⟩`. -/
theorem weilOperator_dual_apply_weilOperator (φ : Module.Dual ℂ W) (x : W) :
    hs.dual.weilOperator φ (hs.weilOperator x) = φ x := by
  rw [weilOperator_dual, LinearMap.dualMap_apply, LinearEquiv.coe_coe, ← weilOperatorEquiv_apply,
    LinearEquiv.symm_apply_apply]

end WeilOperator

section Morphism

variable {W₂ : Type*} [AddCommGroup W₂] [Module ℂ W₂] {ω₂ : Conjugation W₂}

/-- The transpose of a morphism of pure Hodge structures is a morphism between the duals, in the
opposite direction. -/
theorem IsMorphism.dualMap {hs₂ : HodgeStructureOn W₂ ω₂ n} {g : W →ₗ[ℂ] W₂}
    (h : IsMorphism hs hs₂ g) : IsMorphism hs₂.dual hs.dual g.dualMap where
  commutes_conj φ := by
    ext v
    simp [h.commutes_conj]
  map_F_le p := by
    rintro _ ⟨φ, hφ, rfl⟩
    rw [SetLike.mem_coe, dual_F, Submodule.mem_dualAnnihilator] at hφ
    rw [dual_F, Submodule.mem_dualAnnihilator]
    intro x hx
    exact hφ (g x) (h.map_F_le _ ⟨x, hx, rfl⟩)

end Morphism

end HodgeStructureOn

/-! ### The dual of an integral Hodge structure -/

namespace HodgeStructure

variable {V : Type*} {Vℂ : Type*} [AddCommGroup V] [AddCommGroup Vℂ] [Module ℂ Vℂ]
variable {ιℂ : V →ₗ[ℤ] Vℂ} [Module.Free ℤ V] [Module.Finite ℤ V] {hℂ : IsBaseChange ℂ ιℂ}
variable {n : ℤ}

/-- The dual of an integral pure Hodge structure of weight `n`, of weight `-n`. It is carried by
the dual lattice `Hom_ℤ(V, ℤ)`, and its Hodge filtration is that of the dual of the complex Hodge
structure (`HodgeStructure.dual_F`). -/
noncomputable def dual (hs : HodgeStructure hℂ n) :
    HodgeStructure (isBaseChange_dualLatticeMap hℂ) (-n) :=
  (HodgeStructureOn.dual hs).comap (LinearEquiv.refl ℂ _) fun x ↦ by
    rw [latticeConjugation_dual, LinearEquiv.refl_apply, LinearEquiv.refl_apply]

variable (hs : HodgeStructure hℂ n)

/-- The Hodge filtration of the dual of an integral Hodge structure is that of the dual of the
complex Hodge structure. -/
@[simp]
theorem dual_F (p : ℤ) : hs.dual.F p = (HodgeStructureOn.dual hs).F p := by
  rw [dual, HodgeStructureOn.comap_F, LinearEquiv.refl_toLinearMap, Submodule.comap_id]

/-- The Hodge components of the dual of an integral Hodge structure are those of the dual of the
complex Hodge structure. -/
@[simp]
theorem dual_piece (p : ℤ) : hs.dual.piece p = (HodgeStructureOn.dual hs).piece p := by
  rw [dual, HodgeStructureOn.comap_piece, LinearEquiv.refl_toLinearMap, Submodule.comap_id]

/-- The Weil operator of the dual of an integral Hodge structure is the transpose of the inverse
Weil operator. -/
@[simp]
theorem dual_weilOperator :
    hs.dual.weilOperator = hs.weilOperatorEquiv.symm.toLinearMap.dualMap := by
  simp [dual, HodgeStructureOn.weilOperator_comap]

namespace Hom

variable {V₁ V₂ : Type*} {W₁ W₂ : Type*} [AddCommGroup V₁] [AddCommGroup V₂]
variable [AddCommGroup W₁] [Module ℂ W₁] [AddCommGroup W₂] [Module ℂ W₂]
variable {ι₁ : V₁ →ₗ[ℤ] W₁} {ι₂ : V₂ →ₗ[ℤ] W₂} {h₁ : IsBaseChange ℂ ι₁} {h₂ : IsBaseChange ℂ ι₂}
variable [Module.Free ℤ V₁] [Module.Finite ℤ V₁] [Module.Free ℤ V₂] [Module.Finite ℤ V₂]
variable {source : HodgeStructure h₁ n} {target : HodgeStructure h₂ n}

/-- The transpose of a morphism of integral pure Hodge structures, a morphism between the duals in
the opposite direction. -/
noncomputable def dualMap (f : Hom source target) : Hom target.dual source.dual where
  toIntLinearMap := f.toIntLinearMap.dualMap
  map_mem_F p φ hφ := by
    rw [integralMapToComplex_dualMap h₁ h₂, ← toLinearMap_def, dual_F]
    rw [dual_F] at hφ
    exact f.isMorphism.dualMap.map_F_le p ⟨φ, hφ, rfl⟩

/-- The integral map underlying the transpose of a Hodge morphism is the transpose of its integral
map. -/
@[simp]
theorem dualMap_toIntLinearMap (f : Hom source target) :
    f.dualMap.toIntLinearMap = f.toIntLinearMap.dualMap :=
  (rfl)

/-- The transpose of a Hodge morphism acts on a functional by precomposition. -/
@[simp]
theorem dualMap_apply (f : Hom source target) (φ : Module.Dual ℂ W₂) (x : W₁) :
    f.dualMap φ x = φ (f x) := by
  rw [toLinearMap_def, dualMap_toIntLinearMap, integralMapToComplex_dualMap h₁ h₂,
    LinearMap.dualMap_apply, toLinearMap_def]

/-- Transposition sends the zero morphism to the zero morphism. -/
@[simp]
theorem dualMap_zero : (0 : Hom source target).dualMap = 0 := by
  ext φ v
  simp

/-- Transposition is additive. -/
@[simp]
theorem dualMap_add (f g : Hom source target) : (f + g).dualMap = f.dualMap + g.dualMap := by
  ext φ v
  simp

/-- Transposition commutes with negation. -/
@[simp]
theorem dualMap_neg (f : Hom source target) : (-f).dualMap = -f.dualMap := by
  ext φ v
  simp

/-- Transposition commutes with subtraction. -/
@[simp]
theorem dualMap_sub (f g : Hom source target) : (f - g).dualMap = f.dualMap - g.dualMap := by
  ext φ v
  simp

/-- Transposition commutes with natural multiples. -/
@[simp]
theorem dualMap_nsmul (k : ℕ) (f : Hom source target) : (k • f).dualMap = k • f.dualMap := by
  ext φ v
  simp

/-- Transposition commutes with integer multiples. -/
@[simp]
theorem dualMap_zsmul (k : ℤ) (f : Hom source target) : (k • f).dualMap = k • f.dualMap := by
  ext φ v
  simp

/-- The transpose of the identity is the identity. -/
@[simp]
theorem dualMap_id : (id source).dualMap = id source.dual := by
  ext φ
  simp

/-- Transposition reverses composition of Hodge morphisms. -/
@[simp]
theorem dualMap_comp {V₃ W₃ : Type*} [AddCommGroup V₃] [AddCommGroup W₃] [Module ℂ W₃]
    {ι₃ : V₃ →ₗ[ℤ] W₃} {h₃ : IsBaseChange ℂ ι₃} [Module.Free ℤ V₃] [Module.Finite ℤ V₃]
    {third : HodgeStructure h₃ n} (g : Hom target third) (f : Hom source target) :
    (g.comp f).dualMap = f.dualMap.comp g.dualMap := by
  ext φ
  simp [← LinearMap.dualMap_comp_dualMap]

end Hom

end HodgeStructure

end TauCeti.Hodge
