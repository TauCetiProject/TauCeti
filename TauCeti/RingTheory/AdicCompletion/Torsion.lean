/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.Torsion.PrimaryComponent
public import TauCeti.RingTheory.AdicCompletion.AlgHom
public import TauCeti.RingTheory.AdicCompletion.Finite

/-!
# The completion action on ideal-power-torsion modules

An `R`-module in which every element is killed by a power of `I` has a canonical action of
`AdicCompletion I R`. On an element killed by `I ^ n`, a completed scalar acts through its
residue modulo `I ^ n`. The hypothesis is membership of every element in
`Ideal.primaryComponent M I`. No finite generation or Noetherian hypothesis is needed.

`TauCeti.AdicCompletion.torsionModule` constructs this module structure. The residue formula
`AdicCompletion.torsion_smul_eq` characterizes its action. Every `R`-linear map
between such modules is linear for these completion actions, and restriction of scalars recovers
the original action of `R`.

For a finite `R`-module `N`, `TauCeti.AdicCompletion.torsionLiftEquiv` identifies `R`-linear maps
`N → M` with completion-linear maps `AdicCompletion I N → M`; its inverse is restriction along
`AdicCompletion.of`. This is the completion adjunction `Hom_{R̂}(N̂, E) ≃ Hom_R(N, E)` used in
Matlis duality, for `E` an injective hull of the residue field of a Noetherian local ring. No
Noetherian hypothesis is needed: the extension of a linear map evaluates a completed element
through its residue modulo a power of `I` that kills the values of the map.

The construction uses the compatible residues of Mathlib's `AdicCompletion`, formalized by
Judith Ludwig and Christian Merten, and the quotient actions on `Submodule.torsionBySet`.
For its role in Matlis duality, see the Stacks Project,
Section 47.7, Tag 08Z1, and Remark 47.7.9.
-/

public section

noncomputable section

namespace AdicCompletion

variable {R : Type*} [CommRing R] {I : Ideal R}
variable {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

private def torsionActionAt (a : AdicCompletion I R) {n : ℕ} {x : M}
    (hx : x ∈ Submodule.torsionBySet R M ↑(I ^ n)) : M :=
  ↑(evalₐ I n a • (⟨x, hx⟩ : Submodule.torsionBySet R M ↑(I ^ n)))

private theorem torsionActionAt_eq {a : AdicCompletion I R} {x : M} {n : ℕ} {r : R}
    (hx : x ∈ Submodule.torsionBySet R M ↑(I ^ n))
    (ha : evalₐ I n a = Ideal.Quotient.mk (I ^ n) r) :
    torsionActionAt a hx = r • x := by
  simp only [torsionActionAt, ha, Submodule.torsionBySet.mk_smul, Submodule.coe_smul_of_tower]

private theorem torsionActionAt_mono (a : AdicCompletion I R) {x : M} {n m : ℕ}
    (h : n ≤ m) (hx : x ∈ Submodule.torsionBySet R M ↑(I ^ n))
    (hy : x ∈ Submodule.torsionBySet R M ↑(I ^ m)) :
    torsionActionAt a hx = torsionActionAt a hy := by
  obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (evalₐ I m a)
  have hn : evalₐ I n a = Ideal.Quotient.mk (I ^ n) r := by
    rw [← factor_evalₐ h a, ← hr, Ideal.Quotient.factor_mk]
  rw [torsionActionAt_eq hx hn, torsionActionAt_eq hy hr.symm]

variable (hM : ∀ x : M, x ∈ Ideal.primaryComponent M I)

private def torsionAction (a : AdicCompletion I R) (x : M) : M :=
  torsionActionAt a ((Ideal.primaryComponent_mem M I x).mp (hM x)).choose_spec

private theorem torsionAction_eq (a : AdicCompletion I R) {x : M} {n : ℕ}
    (hx : x ∈ Submodule.torsionBySet R M ↑(I ^ n)) :
    torsionAction hM a x = torsionActionAt a hx := by
  let h := (Ideal.primaryComponent_mem M I x).mp (hM x)
  let k := max n h.choose
  have hk : x ∈ Submodule.torsionBySet R M ↑(I ^ k) :=
    Submodule.torsionBySet_le_torsionBySet_pow _ _ (Nat.le_max_left _ _) I hx
  have hchosen : x ∈ Submodule.torsionBySet R M ↑(I ^ h.choose) := h.choose_spec
  exact (torsionActionAt_mono a (Nat.le_max_right _ _) hchosen hk).trans
    (torsionActionAt_mono a (Nat.le_max_left _ _) hx hk).symm

end AdicCompletion

namespace TauCeti.AdicCompletion

open _root_.AdicCompletion

variable {R : Type*} [CommRing R] {I : Ideal R}
variable {M : Type*} [AddCommGroup M] [Module R M]
variable (hM : ∀ x : M, x ∈ Ideal.primaryComponent M I)

/-- The canonical module structure over the completion on a module whose elements are each
annihilated by a power of `I`. Use it with `letI := TauCeti.AdicCompletion.torsionModule hM`. -/
@[instance_reducible]
def torsionModule : Module (AdicCompletion I R) M where
  smul := torsionAction hM
  one_smul x := by
    -- The structure field uses the scalar operation being constructed.
    change torsionAction hM 1 x = x
    obtain ⟨n, hn⟩ := (Ideal.primaryComponent_mem M I x).mp (hM x)
    rw [torsionAction_eq hM 1 hn]
    simp [torsionActionAt]
  mul_smul a b x := by
    -- Expand the scalar operation of this structure before applying its residue formula.
    change torsionAction hM (a * b) x = torsionAction hM a (torsionAction hM b x)
    obtain ⟨n, hn⟩ := (Ideal.primaryComponent_mem M I x).mp (hM x)
    have hb : torsionAction hM b x ∈ Submodule.torsionBySet R M ↑(I ^ n) := by
      rw [torsionAction_eq hM b hn]
      exact (evalₐ I n b • (⟨x, hn⟩ : Submodule.torsionBySet R M ↑(I ^ n))).property
    rw [torsionAction_eq hM (a * b) hn, torsionAction_eq hM a hb]
    have hinner : (⟨torsionAction hM b x, hb⟩ : Submodule.torsionBySet R M ↑(I ^ n)) =
        evalₐ I n b • (⟨x, hn⟩ : Submodule.torsionBySet R M ↑(I ^ n)) :=
      Subtype.ext (torsionAction_eq hM b hn)
    simp only [torsionActionAt, map_mul, mul_smul, hinner]
  smul_zero a := by
    -- The scalar operation is the action defined above.
    change torsionAction hM a 0 = 0
    rw [torsionAction_eq hM a (Submodule.zero_mem (Submodule.torsionBySet R M ↑(I ^ 0)))]
    simp only [torsionActionAt, (Submodule.mk_eq_zero _ _).mpr rfl, smul_zero,
      Submodule.coe_zero]
  smul_add a x y := by
    -- Expand the scalar operation of this structure before applying its residue formula.
    change torsionAction hM a (x + y) = torsionAction hM a x + torsionAction hM a y
    obtain ⟨n, hn⟩ := (Ideal.primaryComponent_mem M I x).mp (hM x)
    obtain ⟨m, hm⟩ := (Ideal.primaryComponent_mem M I y).mp (hM y)
    have hx : x ∈ Submodule.torsionBySet R M ↑(I ^ (max n m)) :=
      Submodule.torsionBySet_le_torsionBySet_pow _ _ (Nat.le_max_left _ _) I hn
    have hy : y ∈ Submodule.torsionBySet R M ↑(I ^ (max n m)) :=
      Submodule.torsionBySet_le_torsionBySet_pow _ _ (Nat.le_max_right _ _) I hm
    rw [torsionAction_eq hM a (Submodule.add_mem _ hx hy), torsionAction_eq hM a hx,
      torsionAction_eq hM a hy]
    have hxy : (⟨x + y, Submodule.add_mem _ hx hy⟩ :
        Submodule.torsionBySet R M ↑(I ^ (max n m))) = ⟨x, hx⟩ + ⟨y, hy⟩ :=
      Subtype.ext (by simp only [Submodule.coe_add])
    simp only [torsionActionAt, hxy, smul_add, Submodule.coe_add]
  add_smul a b x := by
    -- Expand the scalar operation of this structure before applying its residue formula.
    change torsionAction hM (a + b) x = torsionAction hM a x + torsionAction hM b x
    obtain ⟨n, hn⟩ := (Ideal.primaryComponent_mem M I x).mp (hM x)
    rw [torsionAction_eq hM (a + b) hn, torsionAction_eq hM a hn, torsionAction_eq hM b hn]
    simp [torsionActionAt, add_smul]
  zero_smul x := by
    -- The structure field uses the scalar operation being constructed.
    change torsionAction hM 0 x = 0
    obtain ⟨n, hn⟩ := (Ideal.primaryComponent_mem M I x).mp (hM x)
    rw [torsionAction_eq hM 0 hn]
    simp [torsionActionAt]

end TauCeti.AdicCompletion

namespace AdicCompletion

variable {R : Type*} [CommRing R] {I : Ideal R}
variable {M : Type*} [AddCommGroup M] [Module R M]

/-- A completed scalar acts on an element killed by `I ^ n` through its residue modulo
`I ^ n`. This formula permits any representative of the residue. -/
theorem torsion_smul_eq (a : AdicCompletion I R)
    (hM : ∀ x : M, x ∈ Ideal.primaryComponent M I) (x : M) {n : ℕ} (r : R)
    (hx : x ∈ Submodule.torsionBySet R M ↑(I ^ n))
    (ha : evalₐ I n a = Ideal.Quotient.mk (I ^ n) r) :
    letI := TauCeti.AdicCompletion.torsionModule hM
    a • x = r • x := by
  exact (torsionAction_eq hM a hx).trans (torsionActionAt_eq hx ha)

end AdicCompletion

namespace TauCeti.AdicCompletion

variable {R : Type*} [CommRing R] {I : Ideal R}
variable {M : Type*} [AddCommGroup M] [Module R M]
variable (hM : ∀ x : M, x ∈ Ideal.primaryComponent M I)

/-- The canonical completion action extends the scalar tower from `R`. -/
instance torsionModule_isScalarTower :
    letI := torsionModule hM
    IsScalarTower R (AdicCompletion I R) M := by
  let := torsionModule hM
  apply IsScalarTower.of_algebraMap_smul
  intro r x
  obtain ⟨n, hn⟩ := (Ideal.primaryComponent_mem M I x).mp (hM x)
  exact _root_.AdicCompletion.torsion_smul_eq _ hM x r hn
    (_root_.AdicCompletion.evalₐ_of I n r)

end TauCeti.AdicCompletion

namespace LinearMap

variable {R : Type*} [CommRing R] {I : Ideal R}
variable {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
variable (hM : ∀ x : M, x ∈ Ideal.primaryComponent M I)
variable (hN : ∀ y : N, y ∈ Ideal.primaryComponent N I)

/-- An `R`-linear map between ideal-power-torsion modules commutes with the canonical
completion actions. -/
@[simp]
theorem map_adicCompletion_smul (f : M →ₗ[R] N) (a : AdicCompletion I R) (x : M) :
    letI := TauCeti.AdicCompletion.torsionModule hM
    letI := TauCeti.AdicCompletion.torsionModule hN
    f (a • x) = a • f x := by
  obtain ⟨n, hn⟩ := (Ideal.primaryComponent_mem M I x).mp (hM x)
  have hfx : f x ∈ Submodule.torsionBySet R N ↑(I ^ n) := by
    rw [Submodule.mem_torsionBySet_iff] at hn ⊢
    intro r
    rw [← f.map_smul, hn r, f.map_zero]
  obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ I n a)
  rw [a.torsion_smul_eq hM x r hn hr.symm,
    a.torsion_smul_eq hN (f x) r hfx hr.symm, f.map_smul]

end LinearMap

namespace TauCeti.AdicCompletion

variable {R : Type*} [CommRing R] {I : Ideal R}
variable {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
variable (hM : ∀ x : M, x ∈ Ideal.primaryComponent M I)
variable (hN : ∀ y : N, y ∈ Ideal.primaryComponent N I)

/-- Restriction of scalars identifies linear maps for the canonical completion actions with
`R`-linear maps between ideal-power-torsion modules. -/
def torsionRestrictScalarsEquiv :
    letI := TauCeti.AdicCompletion.torsionModule hM
    letI := TauCeti.AdicCompletion.torsionModule hN
    (M →ₗ[AdicCompletion I R] N) ≃ₗ[R] (M →ₗ[R] N) := by
  letI := TauCeti.AdicCompletion.torsionModule hM
  letI := TauCeti.AdicCompletion.torsionModule hN
  exact
    { LinearMap.restrictScalarsₗ R (AdicCompletion I R) M N R with
      invFun := fun f ↦
        { toFun := f
          map_add' := f.map_add
          map_smul' := f.map_adicCompletion_smul hM hN }
      left_inv := fun f ↦ by ext; rfl
      right_inv := fun f ↦ by ext; rfl }

/-- The comparison of Hom modules is restriction of scalars. -/
@[simp]
theorem torsionRestrictScalarsEquiv_apply
    (f : letI := TauCeti.AdicCompletion.torsionModule hM
         letI := TauCeti.AdicCompletion.torsionModule hN
         M →ₗ[AdicCompletion I R] N) (x : M) :
    torsionRestrictScalarsEquiv hM hN f x = f x := (rfl)

/-- Extending a linear map to the canonical completion actions preserves its values. -/
@[simp]
theorem torsionRestrictScalarsEquiv_symm_apply (f : M →ₗ[R] N) (x : M) :
    (torsionRestrictScalarsEquiv hM hN).symm f x = f x := (rfl)

open _root_.AdicCompletion

/-- The extension of `f` through the residues modulo `I ^ n`, for `f` with values killed by
`I ^ n`. -/
private def _root_.AdicCompletion.liftAt (f : N →ₗ[R] M) (n : ℕ)
    (hf : ∀ y, f y ∈ Submodule.torsionBySet R M ↑(I ^ n)) : AdicCompletion I N →ₗ[R] M :=
  (I ^ n • ⊤ : Submodule R N).liftQ f
    (Submodule.smul_le.mpr fun r hr y _ ↦ by
      simpa using (Submodule.mem_torsionBySet_iff _ _).mp (hf y) ⟨r, hr⟩) ∘ₗ
    eval I N n

private theorem _root_.AdicCompletion.liftAt_apply {f : N →ₗ[R] M} {n : ℕ}
    (hf : ∀ y, f y ∈ Submodule.torsionBySet R M ↑(I ^ n)) {x : AdicCompletion I N} {y : N}
    (hx : eval I N n x = Submodule.Quotient.mk y) : liftAt f n hf x = f y := by
  simp only [liftAt, LinearMap.comp_apply, hx, Submodule.liftQ_apply]

private theorem _root_.AdicCompletion.liftAt_smul {f : N →ₗ[R] M} {n : ℕ}
    (hf : ∀ y, f y ∈ Submodule.torsionBySet R M ↑(I ^ n)) (a : AdicCompletion I R)
    (x : AdicCompletion I N) :
    letI := torsionModule hM
    liftAt f n hf (a • x) = a • liftAt f n hf x := by
  let := torsionModule hM
  obtain ⟨y, hy⟩ := Submodule.Quotient.mk_surjective _ (eval I N n x)
  obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (evalₐ I n a)
  have hax : eval I N n (a • x) = Submodule.Quotient.mk (r • y) := by
    rw [eval_apply, smul_eval, val_smul_eq_evalₐ_smul, ← eval_apply, ← hy, ← hr,
      Module.Quotient.mk_smul_mk]
  rw [liftAt_apply hf hax, liftAt_apply hf hy.symm, map_smul,
    a.torsion_smul_eq hM (f y) r (hf y) hr.symm]

/-- `liftAt` as a linear map over the completion. -/
private def liftAtLinear {f : N →ₗ[R] M} {n : ℕ}
    (hf : ∀ y, f y ∈ Submodule.torsionBySet R M ↑(I ^ n)) :
    letI := torsionModule hM
    AdicCompletion I N →ₗ[AdicCompletion I R] M :=
  letI := torsionModule hM
  { liftAt f n hf with map_smul' := liftAt_smul hM hf }

private theorem liftAtLinear_apply {f : N →ₗ[R] M} {n : ℕ}
    (hf : ∀ y, f y ∈ Submodule.torsionBySet R M ↑(I ^ n)) {x : AdicCompletion I N} {y : N}
    (hx : eval I N n x = Submodule.Quotient.mk y) :
    letI := torsionModule hM
    liftAtLinear hM hf x = f y :=
  liftAt_apply hf hx

variable [Module.Finite R N]

/-- Two extensions through residues modulo different powers of `I` agree. -/
private theorem liftAtLinear_eq {f : N →ₗ[R] M} {m n : ℕ}
    (hm : ∀ y, f y ∈ Submodule.torsionBySet R M ↑(I ^ m))
    (hn : ∀ y, f y ∈ Submodule.torsionBySet R M ↑(I ^ n)) :
    letI := torsionModule hM
    liftAtLinear hM hm = liftAtLinear hM hn := by
  let := torsionModule hM
  refine linearMap_ext_of_finite I fun x ↦ ?_
  rw [liftAtLinear_apply hM hm (eval_of I N m x), liftAtLinear_apply hM hn (eval_of I N n x)]

/-- For a finite module `N` and a module `M` whose elements are each killed by a power of `I`,
every `R`-linear map `N → M` extends uniquely to a linear map `AdicCompletion I N → M` over the
completion, for the canonical completion action on `M`. The extension of `f` evaluates a
completed element through its residue modulo `I ^ n`, for any `n` such that `I ^ n` kills the
values of `f` (`torsionLiftEquiv_apply`). Neither a Noetherian hypothesis nor completeness of `R`
is needed. -/
def torsionLiftEquiv :
    letI := torsionModule hM
    (N →ₗ[R] M) ≃ₗ[AdicCompletion I R] (AdicCompletion I N →ₗ[AdicCompletion I R] M) := by
  let := torsionModule hM
  refine LinearEquiv.symm
    { toFun g := g.restrictScalars R ∘ₗ of I N
      map_add' _ _ := by ext; simp
      map_smul' _ _ := by ext; simp
      invFun f := liftAtLinear hM
        (I.exists_forall_mem_torsionBySet_pow_of_mem_primaryComponent f fun _ ↦ hM _).choose_spec
      left_inv g := linearMap_ext_of_finite I fun x ↦ ?_
      right_inv f := LinearMap.ext fun x ↦ ?_ }
  · simpa using liftAtLinear_apply hM
      (I.exists_forall_mem_torsionBySet_pow_of_mem_primaryComponent
        (g.restrictScalars R ∘ₗ of I N) fun _ ↦ hM _).choose_spec
      (eval_of I N _ x)
  · simpa using liftAtLinear_apply hM
      (I.exists_forall_mem_torsionBySet_pow_of_mem_primaryComponent f fun _ ↦ hM _).choose_spec
      (eval_of I N _ x)

/-- The extension of `f` evaluates a completed element through any of its residues modulo a power
`I ^ n` killing the values of `f`. -/
theorem torsionLiftEquiv_apply {f : N →ₗ[R] M} {n : ℕ}
    (hf : ∀ y, f y ∈ Submodule.torsionBySet R M ↑(I ^ n)) {x : AdicCompletion I N} {y : N}
    (hx : eval I N n x = Submodule.Quotient.mk y) : torsionLiftEquiv hM f x = f y := by
  -- `torsionLiftEquiv` is the inverse of a structure whose `invFun` is `liftAtLinear`.
  have h : torsionLiftEquiv hM f =
      liftAtLinear hM
        (I.exists_forall_mem_torsionBySet_pow_of_mem_primaryComponent f fun _ ↦ hM _).choose_spec :=
      (rfl)
  rw [h, liftAtLinear_eq hM _ hf, liftAtLinear_apply hM hf hx]

/-- The extension of `f` agrees with `f` on the image of `N`. -/
@[simp]
theorem torsionLiftEquiv_apply_of (f : N →ₗ[R] M) (x : N) :
    torsionLiftEquiv hM f (of I N x) = f x :=
  torsionLiftEquiv_apply hM
    (I.exists_forall_mem_torsionBySet_pow_of_mem_primaryComponent f fun _ ↦ hM _).choose_spec
    (eval_of I N _ x)

/-- The inverse of `torsionLiftEquiv` restricts a linear map along `AdicCompletion.of`. -/
@[simp]
theorem torsionLiftEquiv_symm_apply
    (g : letI := torsionModule hM
         AdicCompletion I N →ₗ[AdicCompletion I R] M) (x : N) :
    (torsionLiftEquiv hM).symm g x = g (of I N x) := (rfl)

end TauCeti.AdicCompletion
