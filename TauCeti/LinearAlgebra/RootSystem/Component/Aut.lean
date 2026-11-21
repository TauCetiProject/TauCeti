/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.Component.Base
public import TauCeti.LinearAlgebra.RootSystem.Component.Pairing
public import TauCeti.LinearAlgebra.RootSystem.EquivComp
import TauCeti.LinearAlgebra.RootSystem.HomInvariance

/-!
# Equivalences and automorphisms on irreducible components

Functoriality of root-pairing equivalences on irreducible components (`Equiv.componentHom`,
`Equiv.suppEquiv`, `Equiv.supportEquiv`, `Equiv.diagramGraphIso`), intertwining with component
projections (`Equiv.coe_componentProj_weightMap`), and restriction to component pairings over a
field (`componentPairingCongr`, `Equiv.restrictComponent`, `Equiv.restrictComponentAut`,
`Equiv.autCongr_restrictComponentAut`).

## References

* N. Bourbaki, *Lie Groups and Lie Algebras*, Ch. VI §1, no. 2;
  J. S. Milne, *Algebraic Groups* (2017), Appendix C, C.23 and C.55.
-/

public section

open _root_.Equiv (Perm)
open TauCeti (diagramGraph diagramGraph_adj)

namespace RootPairing

section CommRing

variable {ι ι₂ ι₃ R M N M₂ N₂ M₃ N₃ : Type*} [CommRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  [AddCommGroup M₂] [Module R M₂] [AddCommGroup N₂] [Module R N₂]
  [AddCommGroup M₃] [Module R M₃] [AddCommGroup N₃] [Module R N₃]
  {P : RootPairing ι R M N} {Q : RootPairing ι₂ R M₂ N₂} {S : RootPairing ι₃ R M₃ N₃}

/-! ### Functoriality on components and blocks -/

@[simp] theorem Equiv.nonorthogonalGraphIso_id :
    (Equiv.id P).nonorthogonalGraphIso = SimpleGraph.Iso.refl := by ext i; simp

@[simp] theorem Equiv.nonorthogonalGraphIso_comp (e : P.Equiv Q) (f : Q.Equiv S) :
    (Equiv.comp f e).nonorthogonalGraphIso =
      e.nonorthogonalGraphIso.trans f.nonorthogonalGraphIso := by ext i; simp

@[simp] theorem Equiv.nonorthogonalGraphIso_symm (e : P.Equiv Q) :
    (Equiv.symm P Q e).nonorthogonalGraphIso = e.nonorthogonalGraphIso.symm := by
  ext i
  exact e.indexEquiv.injective (by
    rw [nonorthogonalGraphIso_apply, inv_indexEquiv, _root_.Equiv.apply_symm_apply,
      ← nonorthogonalGraphIso_apply]; simp)

@[simp] theorem Equiv.componentEquiv_id :
    (Equiv.id P).componentEquiv = _root_.Equiv.refl P.Component :=
  _root_.Equiv.ext fun C ↦ C.ind fun _ ↦ by simp

@[simp] theorem Equiv.componentEquiv_comp (e : P.Equiv Q) (f : Q.Equiv S) :
    (Equiv.comp f e).componentEquiv = e.componentEquiv.trans f.componentEquiv :=
  _root_.Equiv.ext fun C ↦ C.ind fun _ ↦ by simp

@[simp] theorem Equiv.componentEquiv_symm (e : P.Equiv Q) :
    (Equiv.symm P Q e).componentEquiv = e.componentEquiv.symm :=
  _root_.Equiv.ext fun C ↦ C.ind fun _ ↦ by simp

/-- The action of the automorphism group of a root pairing on its irreducible components. -/
def Equiv.componentHom (P : RootPairing ι R M N) : P.Aut →* Perm P.Component where
  toFun σ := σ.componentEquiv
  map_one' := Equiv.componentEquiv_id
  map_mul' σ τ := Equiv.componentEquiv_comp τ σ

@[simp] theorem Equiv.componentEquiv_one : (1 : P.Aut).componentEquiv = (1 : Perm P.Component) :=
  (Equiv.componentHom P).map_one

theorem Equiv.componentEquiv_mul (σ τ : P.Aut) :
    (σ * τ).componentEquiv = σ.componentEquiv * τ.componentEquiv :=
  (Equiv.componentHom P).map_mul σ τ

section AutPowers

variable (σ : P.Aut)

@[simp] theorem Equiv.componentHom_apply : Equiv.componentHom P σ = σ.componentEquiv := (rfl)

@[simp] theorem Equiv.componentEquiv_inv : (σ⁻¹).componentEquiv = (σ.componentEquiv)⁻¹ :=
  (Equiv.componentHom P).map_inv σ

@[simp] theorem Equiv.componentEquiv_pow (n : ℕ) : (σ ^ n).componentEquiv = σ.componentEquiv ^ n :=
  (Equiv.componentHom P).map_pow σ n

@[simp] theorem Equiv.componentEquiv_zpow (z : ℤ) : (σ ^ z).componentEquiv = σ.componentEquiv ^ z :=
  (Equiv.componentHom P).map_zpow σ z

end AutPowers

/-- Every root reflection fixes every irreducible component. -/
@[simp] theorem Equiv.componentEquiv_reflection (i : ι) :
    (Equiv.reflection P i).componentEquiv = (1 : Perm P.Component) :=
  _root_.Equiv.ext fun C ↦ C.ind fun j ↦
    ((Equiv.reflection P i).componentEquiv_componentOf j).trans (P.componentOf_reflectionPerm i j)

section EquivAction

variable (e : P.Equiv Q)

/-- The bijection `C.supp ≃ (e.componentEquiv C).supp` induced by an equivalence. -/
def Equiv.suppEquiv (C : P.Component) : C.supp ≃ (e.componentEquiv C).supp where
  toFun i := ⟨e.indexEquiv i, e.indexEquiv_mem_supp_iff.mpr i.2⟩
  invFun j := ⟨e.indexEquiv.symm j, e.indexEquiv_mem_supp_iff.mp (by simp)⟩
  left_inv i := Subtype.ext (e.indexEquiv.symm_apply_apply i)
  right_inv j := Subtype.ext (e.indexEquiv.apply_symm_apply j)

@[simp] theorem Equiv.coe_suppEquiv_apply (C : P.Component) (i : C.supp) :
    (e.suppEquiv C i : ι₂) = e.indexEquiv i := (rfl)

@[simp] theorem Equiv.coe_suppEquiv_symm_apply (C : P.Component) (j : (e.componentEquiv C).supp) :
    ((e.suppEquiv C).symm j : ι) = e.indexEquiv.symm j := (rfl)

/-- An equivalence maps the root block of `C` onto the root block of `e.componentEquiv C`. -/
theorem Equiv.image_indexEquiv_supp (C : P.Component) :
    e.indexEquiv '' (C.supp : Set ι) = (e.componentEquiv C).supp := by
  ext j
  exact ⟨fun ⟨_, hi, h⟩ ↦ h ▸ e.indexEquiv_mem_supp_iff.mpr hi, fun hj ↦
    ⟨e.indexEquiv.symm j, e.indexEquiv_mem_supp_iff.mp (by simp [hj]),
      e.indexEquiv.apply_symm_apply j⟩⟩

theorem Equiv.weightMap_mem_componentSpace {C : P.Component} {x : M} (hx : x ∈ P.componentSpace C) :
    e.weightMap x ∈ Q.componentSpace (e.componentEquiv C) :=
  e.map_componentSpace C ▸ Submodule.mem_map_of_mem hx

theorem Equiv.coweightMap_mem_corootComponentSpace {C : P.Component} {y : N₂}
    (hy : y ∈ Q.corootComponentSpace (e.componentEquiv C)) :
    e.coweightMap y ∈ P.corootComponentSpace C :=
  e.map_corootComponentSpace C ▸ Submodule.mem_map_of_mem hy

end EquivAction

/-! ### Compatibility with component projections -/

section Projection

variable [P.IsRootSystem] [Q.IsRootSystem]

/-- **An equivalence of root systems intertwines the component projections.** -/
theorem Equiv.coe_componentProj_weightMap (e : P.Equiv Q) (C : P.Component) (x : M) :
    (Q.componentProj (e.componentEquiv C) (e.weightMap x) : M₂) =
      e.weightMap (P.componentProj C x) := by
  refine LinearMap.congr_fun (LinearMap.ext_on_range (IsRootSystem.span_root_eq_top (P := P))
    (f := (Q.componentSpace (e.componentEquiv C)).subtype ∘ₗ
      Q.componentProj (e.componentEquiv C) ∘ₗ e.weightMap)
    (g := e.weightMap ∘ₗ (P.componentSpace C).subtype ∘ₗ P.componentProj C) fun j ↦ ?_) x
  simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype,
    Hom.root_weightMap_apply P Q j e.toHom]
  by_cases hj : P.componentOf j = C
  · subst hj
    have hmem : Q.root (e.indexEquiv j) ∈ Q.componentSpace (e.componentEquiv (P.componentOf j)) :=
      e.componentEquiv_componentOf j ▸ Q.root_mem_componentSpace (e.indexEquiv j)
    rw [Q.componentProj_apply_of_mem hmem, P.componentProj_root_self]
    exact (Hom.root_weightMap_apply P Q j e.toHom).symm
  · have hj' : Q.componentOf (e.indexEquiv j) ≠ e.componentEquiv C :=
      e.componentEquiv_componentOf j ▸ e.componentEquiv.injective.ne hj
    simp [Q.componentProj_root_of_ne hj', P.componentProj_root_of_ne hj]

/-- Powers of an automorphism intertwine component projections along permutation powers. -/
theorem Equiv.coe_componentProj_pow_weightMap (σ : P.Aut) (n : ℕ) (C : P.Component) (x : M) :
    (P.componentProj ((σ.componentEquiv ^ n) C) ((σ.weightMap ^ n) x) : M) =
      (σ.weightMap ^ n) (P.componentProj C x) := by
  rw [← σ.componentEquiv_pow, ← σ.weightMap_pow]; exact (σ ^ n).coe_componentProj_weightMap C x

end Projection

/-! ### Compatibility with bases and Dynkin-diagram components -/

section Base

variable (e : P.Equiv Q) {b : P.Base} {b' : Q.Base}
  (hb : ∀ i, i ∈ b.support ↔ e.indexEquiv i ∈ b'.support)

/-- The bijection `b.support ≃ b'.support` induced by a base-preserving equivalence. -/
def Equiv.supportEquiv : b.support ≃ b'.support where
  toFun i := ⟨e.indexEquiv i, (hb i).mp i.2⟩
  invFun j := ⟨e.indexEquiv.symm j, (hb _).mpr (by simp [j.2])⟩
  left_inv i := Subtype.ext (e.indexEquiv.symm_apply_apply i)
  right_inv j := Subtype.ext (e.indexEquiv.apply_symm_apply j)

@[simp] theorem Equiv.coe_supportEquiv_apply (i : b.support) :
    (e.supportEquiv hb i : ι₂) = e.indexEquiv i := (rfl)

@[simp] theorem Equiv.coe_supportEquiv_symm_apply (j : b'.support) :
    ((e.supportEquiv hb).symm j : ι) = e.indexEquiv.symm j := (rfl)

end Base

section CrystallographicBase

variable [CharZero R] [P.IsCrystallographic] [Q.IsCrystallographic]
  (e : P.Equiv Q) {b : P.Base} {b' : Q.Base}
  (hb : ∀ i, i ∈ b.support ↔ e.indexEquiv i ∈ b'.support)

/-- A base-preserving equivalence preserves Cartan matrix entries along `supportEquiv`. -/
@[simp] theorem Equiv.cartanMatrix_supportEquiv (i j : b.support) :
    b'.cartanMatrix (e.supportEquiv hb i) (e.supportEquiv hb j) = b.cartanMatrix i j := by
  refine FaithfulSMul.algebraMap_injective ℤ R ?_
  rw [b'.algebraMap_cartanMatrixIn_apply ℤ, b.algebraMap_cartanMatrixIn_apply ℤ]
  exact e.toHom.pairing

/-- The Dynkin-diagram isomorphism induced by a base-preserving equivalence. -/
def Equiv.diagramGraphIso : diagramGraph b.cartanMatrix ≃g diagramGraph b'.cartanMatrix where
  toEquiv := e.supportEquiv hb
  map_rel_iff' {i j} := by
    simp only [diagramGraph_adj, ne_eq, (e.supportEquiv hb).apply_eq_iff_eq,
      e.cartanMatrix_supportEquiv hb]

@[simp] theorem Equiv.diagramGraphIso_apply (i : b.support) :
    e.diagramGraphIso hb i = e.supportEquiv hb i := (rfl)

/-- **For a base-preserving equivalence, `componentEquiv` agrees with `diagramGraphIso`.** -/
theorem Equiv.componentEquiv_base_componentEquiv [IsDomain R] [Finite ι] [Finite ι₂]
    [P.IsReduced] [Q.IsReduced] (K : (diagramGraph b.cartanMatrix).ConnectedComponent) :
    e.componentEquiv (b.componentEquiv K) =
      b'.componentEquiv ((e.diagramGraphIso hb).connectedComponentEquiv K) :=
  K.ind fun _ ↦ by simp

end CrystallographicBase

end CommRing

/-! ### Restricting equivalences and automorphisms to component pairings -/

section Field

variable {ι ι₂ K M N M₂ N₂ : Type*} [Field K]
  [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]
  [AddCommGroup M₂] [Module K M₂] [AddCommGroup N₂] [Module K N₂]
  {P : RootPairing ι K M N} {Q : RootPairing ι₂ K M₂ N₂}
  [Finite ι] [Finite ι₂] [P.IsRootSystem] [Q.IsRootSystem]

variable (P) in
/-- The canonical equivalence between the component pairings of equal components `C = D`, whose
coercions to `M`, `N`, and `ι` are definitionally the identity. -/
noncomputable def componentPairingCongr {C D : P.Component} (h : C = D) :
    (P.componentPairing C).Equiv (P.componentPairing D) where
  weightMap := (LinearEquiv.ofEq _ _ (congrArg P.componentSpace h)).toLinearMap
  coweightMap := (LinearEquiv.ofEq _ _ (congrArg P.corootComponentSpace h.symm)).toLinearMap
  indexEquiv := _root_.Equiv.subtypeEquivRight fun _ ↦ by rw [h]
  weight_coweight_transpose := by subst h; ext y x; simp
  root_weightMap := by subst h; ext i; simp
  coroot_coweightMap := by subst h; ext i; simp
  bijective_weightMap := (LinearEquiv.ofEq _ _ _).bijective
  bijective_coweightMap := (LinearEquiv.ofEq _ _ _).bijective

section CongrLemmas

variable {C D : P.Component} (h : C = D)

@[simp] theorem coe_componentPairingCongr_weightMap (x : P.componentSpace C) :
    ((P.componentPairingCongr h).weightMap x : M) = x := (rfl)

@[simp] theorem coe_componentPairingCongr_coweightMap (y : P.corootComponentSpace D) :
    ((P.componentPairingCongr h).coweightMap y : N) = y := (rfl)

@[simp] theorem coe_componentPairingCongr_indexEquiv (i : C.supp) :
    ((P.componentPairingCongr h).indexEquiv i : ι) = i := (rfl)

@[simp] theorem coe_componentPairingCongr_indexEquiv_symm (j : D.supp) :
    ((P.componentPairingCongr h).indexEquiv.symm j : ι) = j := (rfl)

end CongrLemmas

@[simp] theorem componentPairingCongr_refl (C : P.Component) :
    P.componentPairingCongr (rfl : C = C) = Equiv.id (P.componentPairing C) := by ext x <;> rfl

section RestrictComponent

variable (e : P.Equiv Q) (C : P.Component)

/-- **Restriction of a root-pairing equivalence to an irreducible component.** -/
noncomputable def Equiv.restrictComponent :
    (P.componentPairing C).Equiv (Q.componentPairing (e.componentEquiv C)) where
  weightMap :=
    (e.weightEquiv.ofSubmodules (P.componentSpace C) (Q.componentSpace (e.componentEquiv C))
      (e.map_componentSpace C)).toLinearMap
  coweightMap :=
    (e.coweightEquiv.ofSubmodules (Q.corootComponentSpace (e.componentEquiv C))
      (P.corootComponentSpace C) (e.map_corootComponentSpace C)).toLinearMap
  indexEquiv := e.suppEquiv C
  weight_coweight_transpose := by
    ext y x; simpa [LinearMap.dualMap_apply] using e.toLinearMap_weightEquiv (x : M) (y : N₂)
  root_weightMap := by ext i; simpa using Hom.root_weightMap_apply P Q (i : ι) e.toHom
  coroot_coweightMap := by ext j; simpa using Hom.coroot_coweightMap_apply P Q (j : ι₂) e.toHom
  bijective_weightMap := LinearEquiv.bijective _
  bijective_coweightMap := LinearEquiv.bijective _

@[simp] theorem Equiv.coe_restrictComponent_weightMap (x : P.componentSpace C) :
    ((e.restrictComponent C).weightMap x : M₂) = e.weightMap x := (rfl)

theorem Equiv.coe_restrictComponent_weightEquiv (x : P.componentSpace C) :
    ((e.restrictComponent C).weightEquiv x : M₂) = e.weightMap x := (rfl)

@[simp] theorem Equiv.coe_restrictComponent_weightEquiv_symm
    (x : Q.componentSpace (e.componentEquiv C)) :
    ((e.restrictComponent C).weightEquiv.symm x : M) = e.weightEquiv.symm x :=
  e.weightEquiv.injective (by simp [← coe_restrictComponent_weightMap])

@[simp] theorem Equiv.coe_restrictComponent_coweightMap
    (y : Q.corootComponentSpace (e.componentEquiv C)) :
    ((e.restrictComponent C).coweightMap y : N) = e.coweightMap y := (rfl)

theorem Equiv.coe_restrictComponent_coweightEquiv
    (y : Q.corootComponentSpace (e.componentEquiv C)) :
    ((e.restrictComponent C).coweightEquiv y : N) = e.coweightMap y := (rfl)

@[simp] theorem Equiv.coe_restrictComponent_coweightEquiv_symm (y : P.corootComponentSpace C) :
    ((e.restrictComponent C).coweightEquiv.symm y : N₂) = e.coweightEquiv.symm y :=
  e.coweightEquiv.injective (by simp [← coe_restrictComponent_coweightMap])

@[simp] theorem Equiv.coe_restrictComponent_indexEquiv (i : C.supp) :
    ((e.restrictComponent C).indexEquiv i : ι₂) = e.indexEquiv i := (rfl)

@[simp] theorem Equiv.coe_restrictComponent_indexEquiv_symm (j : (e.componentEquiv C).supp) :
    ((e.restrictComponent C).indexEquiv.symm j : ι) = e.indexEquiv.symm j := (rfl)

end RestrictComponent

/-- A base-preserving equivalence carries simple roots in `C` to simple roots in
`e.componentEquiv C`. -/
theorem Equiv.mem_support_restrictComponent_indexEquiv_iff (e : P.Equiv Q) {b : P.Base}
    {b' : Q.Base} (hb : ∀ i, i ∈ b.support ↔ e.indexEquiv i ∈ b'.support) (C : P.Component)
    (i : C.supp) :
    ((e.restrictComponent C).indexEquiv i : ι₂) ∈ b'.support ↔ (i : ι) ∈ b.support := (hb i).symm

section RestrictComponentAut

variable (τ : P.Aut) (C : P.Component) (hC : τ.componentEquiv C = C)

/-- **Restriction of a component-fixing automorphism to the component pairing.** -/
noncomputable def Equiv.restrictComponentAut : (P.componentPairing C).Aut :=
  Equiv.comp (P.componentPairingCongr hC) (τ.restrictComponent C)

@[simp] theorem Equiv.coe_restrictComponentAut_weightMap (x : P.componentSpace C) :
    ((τ.restrictComponentAut C hC).weightMap x : M) = τ.weightMap x := (rfl)

theorem Equiv.coe_restrictComponentAut_weightEquiv (x : P.componentSpace C) :
    ((τ.restrictComponentAut C hC).weightEquiv x : M) = τ.weightMap x := (rfl)

@[simp] theorem Equiv.coe_restrictComponentAut_coweightMap (y : P.corootComponentSpace C) :
    ((τ.restrictComponentAut C hC).coweightMap y : N) = τ.coweightMap y := (rfl)

@[simp] theorem Equiv.coe_restrictComponentAut_indexEquiv (i : C.supp) :
    ((τ.restrictComponentAut C hC).indexEquiv i : ι) = τ.indexEquiv i := (rfl)

@[simp] theorem Equiv.coe_restrictComponentAut_indexEquiv_symm (i : C.supp) :
    ((τ.restrictComponentAut C hC).indexEquiv.symm i : ι) = τ.indexEquiv.symm i := (rfl)

end RestrictComponentAut

theorem Equiv.restrictComponentAut_congr {τ₁ τ₂ : P.Aut} {C : P.Component}
    (h : τ₁ = τ₂) (h₁ : τ₁.componentEquiv C = C) (h₂ : τ₂.componentEquiv C = C) :
    τ₁.restrictComponentAut C h₁ = τ₂.restrictComponentAut C h₂ := by subst h; rfl

@[simp] theorem Equiv.restrictComponentAut_one (C : P.Component) :
    (1 : P.Aut).restrictComponentAut C (by simp) = 1 := by ext x <;> rfl

theorem Equiv.restrictComponentAut_mul {τ₁ τ₂ : P.Aut} {C : P.Component}
    (h₁ : τ₁.componentEquiv C = C) (h₂ : τ₂.componentEquiv C = C) :
    (τ₁ * τ₂).restrictComponentAut C (by simp [h₁, h₂]) =
      τ₁.restrictComponentAut C h₁ * τ₂.restrictComponentAut C h₂ := by ext x <;> rfl

@[simp] theorem Equiv.restrictComponentAut_inv {τ : P.Aut} {C : P.Component}
    (hC : τ.componentEquiv C = C) :
    (τ⁻¹).restrictComponentAut C (by rw [componentEquiv_inv, Perm.inv_eq_iff_eq, hC]) =
      (τ.restrictComponentAut C hC)⁻¹ :=
  eq_inv_of_mul_eq_one_left <| by
    rw [← restrictComponentAut_mul, restrictComponentAut_congr (inv_mul_cancel τ) _ (by simp),
      restrictComponentAut_one]

@[simp] theorem Equiv.restrictComponentAut_pow {τ : P.Aut} {C : P.Component}
    (hC : τ.componentEquiv C = C) (n : ℕ) :
    (τ ^ n).restrictComponentAut C
        (by rw [componentEquiv_pow]; exact Function.IsFixedPt.perm_pow hC n) =
      τ.restrictComponentAut C hC ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hpow : (τ ^ n).componentEquiv C = C := by
      rw [componentEquiv_pow]; exact Function.IsFixedPt.perm_pow hC n
    simp only [pow_succ', restrictComponentAut_mul hC hpow, ih]

/-- **Conjugating `τ.restrictComponentAut C hC` along `e.restrictComponent C` restricts
`e.autCongr τ` to `e.componentEquiv C`.** -/
theorem Equiv.autCongr_restrictComponentAut (e : P.Equiv Q) {τ : P.Aut} {C : P.Component}
    (hC : τ.componentEquiv C = C) :
    (e.restrictComponent C).autCongr (τ.restrictComponentAut C hC) =
      (e.autCongr τ).restrictComponentAut (e.componentEquiv C) (by simp [autCongr_apply, hC]) := by
  ext x <;> simp [autCongr_apply]

/-- A base-preserving automorphism fixing `C` permutes the simple roots of `b` lying in `C`. -/
theorem Equiv.mem_support_restrictComponentAut_indexEquiv_iff {τ : P.Aut} {b : P.Base}
    (hb : ∀ i, i ∈ b.support ↔ τ.indexEquiv i ∈ b.support) {C : P.Component}
    (hC : τ.componentEquiv C = C) (i : C.supp) :
    ((τ.restrictComponentAut C hC).indexEquiv i : ι) ∈ b.support ↔ (i : ι) ∈ b.support :=
  (hb i).symm

end Field

end RootPairing
