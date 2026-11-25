/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.FGModuleCat.Generator.Basic
public import TauCeti.RingTheory.Morita.Progenerator

import Mathlib.Algebra.Category.ModuleCat.Injective
import TauCeti.Algebra.Category.FGModuleCat.Generator.Endomorphism
import TauCeti.Algebra.Module.Injective.AdditiveClosure

/-!
# The Morita-Tachikawa correspondence: injectivity on marked pairs

Let `A` and `A'` be Artin algebras over a commutative Artinian ring `R`, with generator-cogenerators
`M` of `mod A` and `M'` of `mod A'`. If the endomorphism algebras `Module.End A M` and
`Module.End A' M'` are isomorphic as `R`-algebras, then an `R`-linear equivalence
`mod A ≌ mod A'` carries `M` to `M'` (`TauCeti.exists_linear_equivalence_of_algEquiv_end`). With
the two directions in `TauCeti.RingTheory.Morita.Tachikawa`, this makes `(A, M) ↦ Module.End A M` a
bijection from such pairs, up to equivalence, onto the Artin algebras of dominant dimension at least
two, up to isomorphism.

Write `Γ = Module.End A M`, acting on `M` by evaluation. The proof recovers `A` and `M` from `Γ`:

1. `M` is finitely generated, projective and injective over `Γ`, and `A ≅ Module.End Γ M` by the
   double centralizer property of a generator (`TauCeti.algEquivEndEndOfIsGenerator`).
2. Through `e`, the module `M'` becomes a `Γ`-module `Y`, again finitely generated, projective and
   injective, with `A' ≅ Module.End Γ Y`.
3. Over `Γ`, the finitely generated projective-injective modules are the retracts of finite powers
   of `M` (`TauCeti.exists_comp_eq_id_pi_of_projective_of_injective`). The same holds for `Y`, so
   each of `M` and `Y` is a retract of a finite power of the other.
4. Two modules `X` and `Y` with this property have Morita equivalent endomorphism rings, by an
   equivalence carrying `X` to `Y` (`TauCeti.exists_moritaEquivalence_moduleEnd_of_comp_eq_id`).
   Both `Module.End Γ X` and `Module.End Γ Y` are corners of `C = Module.End Γ (X × Y)`, at full
   idempotents, and the corner functors send the `C`-module `X × Y` to `X` and to `Y`.

The multiplicities of `M` are kept: `M` goes to `M'` itself, not only `add M` to `add M'`.

## Main results

* `TauCeti.exists_moritaEquivalence_moduleEnd_of_comp_eq_id`: if each of two modules is a retract
  of a finite power of the other, a Morita equivalence between their endomorphism rings carries one
  to the other.
* `TauCeti.exists_moritaEquivalence_functor_obj_iso_of_algEquiv_end`: the correspondence at the
  level of all modules.
* `TauCeti.exists_linear_equivalence_of_algEquiv_end`: **the Morita-Tachikawa correspondence,
  injectivity on marked pairs**.

## Implementation notes

`TauCeti.RingTheory.Idempotents.Corner.Retract` identifies the endomorphism ring of a retract with
a corner of the *opposite* endomorphism ring, the convention in which the regular module recovers
its ring. Here the modules `M` and `Y` themselves must be tracked, as modules over `Module.End Γ M`
and `Module.End Γ Y` acting by evaluation, so this file uses corners of the endomorphism ring
itself (`TauCeti.cornerModuleEndAlgEquiv`). The corner functor of
`IsIdempotentElem.cornerEquivalence` is explicit, `V ↦ eV`, which computes the image of the
`C`-module `X × Y` (`TauCeti.smulTopRetractAddEquiv`).

## References

* B. J. Müller, *The classification of algebras by dominant dimension*, Canad. J. Math. 20 (1968),
  398–409, Theorem 2.
* M. Auslander, I. Reiten, S. O. Smalø, *Representation Theory of Artin Algebras*, Cambridge
  Studies in Advanced Mathematics 36, CUP (1995), Section VI.5.
-/

public section

open CategoryTheory
open scoped ModuleCat.Algebra Pointwise

universe u

namespace TauCeti

/-! ### Corners of endomorphism rings at retracts -/

section Corner

variable {A : Type*} [Ring A] {X : Type*} [AddCommGroup X] [Module A X]
  {M : Type*} [AddCommGroup M] [Module A M] {i : X →ₗ[A] M} {p : M →ₗ[A] X}

/-- The idempotent `i ∘ p` of `End_A M` attached to a retract `X` of `M`, with inclusion `i` and
retraction `p`. -/
theorem isIdempotentElem_comp_of_comp_eq_id (hip : p ∘ₗ i = .id) :
    IsIdempotentElem (i ∘ₗ p : Module.End A M) := by
  have h : ∀ y, p (i y) = y := LinearMap.congr_fun hip
  unfold IsIdempotentElem
  ext x
  simp [h]

/-- An endomorphism of `M` factoring through its retract `X` lies in the two-sided ideal generated
by the idempotent of `X`. -/
private theorem comp_mem_span_comp (hip : p ∘ₗ i = .id) (u : X →ₗ[A] M) (v : M →ₗ[A] X) :
    (u ∘ₗ v : Module.End A M) ∈ TwoSidedIdeal.span {(i ∘ₗ p : Module.End A M)} := by
  have h : ∀ y, p (i y) = y := LinearMap.congr_fun hip
  have key : (u ∘ₗ v : Module.End A M) =
      (u ∘ₗ p : Module.End A M) * (i ∘ₗ p : Module.End A M) * (i ∘ₗ v : Module.End A M) := by
    ext x
    simp [h]
  rw [key]
  exact TwoSidedIdeal.mul_mem_right _ _ _
    (TwoSidedIdeal.mul_mem_left _ _ _ (TwoSidedIdeal.subset_span rfl))

variable {Y : Type*} [AddCommGroup Y] [Module A Y]

/-- If `M = X ⊕ Y` and `id_Y` is a finite sum of maps factoring through `X`, that is, `Y` is a
retract of a finite power of `X`, then the idempotent of `X` is full in `End_A M`. -/
theorem span_comp_eq_top_of_sum_comp_eq_id (hip : p ∘ₗ i = .id) {i' : Y →ₗ[A] M}
    {p' : M →ₗ[A] Y} (hsum : i ∘ₗ p + i' ∘ₗ p' = .id) {ι : Type*} (s : Finset ι)
    (u : ι → X →ₗ[A] Y) (v : ι → Y →ₗ[A] X) (huv : ∑ j ∈ s, u j ∘ₗ v j = .id) :
    TwoSidedIdeal.span {(i ∘ₗ p : Module.End A M)} = ⊤ := by
  refine (TwoSidedIdeal.one_mem_iff _).mp ?_
  have key : (1 : Module.End A M) = (i ∘ₗ p : Module.End A M) +
      ∑ j ∈ s, ((i' ∘ₗ u j) ∘ₗ (v j ∘ₗ p') : Module.End A M) := by
    ext x
    have hx := LinearMap.congr_fun hsum x
    have hy := LinearMap.congr_fun huv (p' x)
    simp only [LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.id_apply] at hy
    simpa [LinearMap.sum_apply, ← map_sum, hy] using hx.symm
  rw [key]
  exact add_mem (TwoSidedIdeal.subset_span rfl) (sum_mem fun j _ ↦ comp_mem_span_comp hip _ _)

private theorem comp_corner_val (hip : p ∘ₗ i = .id)
    (c : (isIdempotentElem_comp_of_comp_eq_id hip).Corner) (x : M) :
    i (p ((c.val : Module.End A M) x)) = (c.val : Module.End A M) x :=
  LinearMap.congr_fun ((isIdempotentElem_comp_of_comp_eq_id hip).mul_corner_val c) x

private theorem corner_val_comp (hip : p ∘ₗ i = .id)
    (c : (isIdempotentElem_comp_of_comp_eq_id hip).Corner) (x : M) :
    (c.val : Module.End A M) (i (p x)) = (c.val : Module.End A M) x :=
  LinearMap.congr_fun ((isIdempotentElem_comp_of_comp_eq_id hip).corner_val_mul c) x

/-- **The piece of a retract.** For the idempotent `e = i ∘ p` of a retract `X` of `M`, the piece
`eM = e • M` of `M` is a copy of `X`, by `i`. -/
def smulTopRetractAddEquiv (hip : p ∘ₗ i = .id) :
    X ≃+ ↥((i ∘ₗ p : Module.End A M) • (⊤ : Submodule ℤ M)) where
  toFun x := ⟨i x, (isIdempotentElem_comp_of_comp_eq_id hip).mem_smul_top_iff_smul_eq_self.2
    (by simp [Module.End.smul_def, show p (i x) = x from LinearMap.congr_fun hip x])⟩
  invFun z := p z
  left_inv x := LinearMap.congr_fun hip x
  right_inv z := Subtype.ext
    ((isIdempotentElem_comp_of_comp_eq_id hip).smul_eq_self_of_mem_smul_top z.property)
  map_add' x y := Subtype.ext (map_add i x y)

@[simp]
theorem coe_smulTopRetractAddEquiv_apply (hip : p ∘ₗ i = .id) (x : X) :
    (smulTopRetractAddEquiv hip x : M) = i x :=
  (rfl)

@[simp]
theorem smulTopRetractAddEquiv_symm_apply (hip : p ∘ₗ i = .id)
    (z : ↥((i ∘ₗ p : Module.End A M) • (⊤ : Submodule ℤ M))) :
    (smulTopRetractAddEquiv hip).symm z = p z :=
  (rfl)

variable (R : Type*) [CommSemiring R] [Algebra R A] [Module R X] [IsScalarTower R A X]
  [Module R M] [IsScalarTower R A M]

/-- **The endomorphism ring of a retract is a corner.** If `X` is a retract of `M`, with inclusion
`i` and retraction `p`, the corner of `End_A M` at the idempotent `i ∘ p` is `End_A X`, by
`f ↦ p ∘ f ∘ i`. -/
noncomputable def cornerModuleEndAlgEquiv (hip : p ∘ₗ i = .id) :
    (isIdempotentElem_comp_of_comp_eq_id hip).Corner ≃ₐ[R] Module.End A X where
  toFun c := p ∘ₗ (c.val : Module.End A M) ∘ₗ i
  invFun g := (isIdempotentElem_comp_of_comp_eq_id hip).compress (i ∘ₗ g ∘ₗ p)
  left_inv c := by
    have hpi : ∀ y, p (i y) = y := LinearMap.congr_fun hip
    apply Subtype.ext
    ext x
    simp [hpi, comp_corner_val hip c, corner_val_comp hip c]
  right_inv g := by
    have hpi : ∀ y, p (i y) = y := LinearMap.congr_fun hip
    ext x
    simp [hpi]
  map_mul' c c' := by
    ext x
    simp [corner_val_comp hip c]
  map_add' c c' := by
    ext x
    simp
  commutes' r := by
    have hpi : ∀ y, p (i y) = y := LinearMap.congr_fun hip
    ext x
    simp [hpi]

@[simp]
theorem cornerModuleEndAlgEquiv_apply (hip : p ∘ₗ i = .id)
    (c : (isIdempotentElem_comp_of_comp_eq_id hip).Corner) :
    cornerModuleEndAlgEquiv R hip c = p ∘ₗ (c.val : Module.End A M) ∘ₗ i :=
  (rfl)

@[simp]
theorem val_cornerModuleEndAlgEquiv_symm_apply (hip : p ∘ₗ i = .id) (g : Module.End A X) :
    ((cornerModuleEndAlgEquiv R hip).symm g).val = i ∘ₗ g ∘ₗ p := by
  have hpi : ∀ y, p (i y) = y := LinearMap.congr_fun hip
  refine ((isIdempotentElem_comp_of_comp_eq_id hip).val_compress _).trans ?_
  ext x
  simp [hpi]

/-- The copy `smulTopRetractAddEquiv` of `X` in `M` turns the action of the corner on `eM` into
the action of `End_A X` on `X`. -/
theorem smulTopRetractAddEquiv_smul (hip : p ∘ₗ i = .id)
    (c : (isIdempotentElem_comp_of_comp_eq_id hip).Corner) (x : X) :
    smulTopRetractAddEquiv hip (cornerModuleEndAlgEquiv R hip c x) =
      c • smulTopRetractAddEquiv hip x :=
  Subtype.ext (comp_corner_val hip c (i x))

/-- The retraction `p : eM → X` turns the action of `End_A X`, through the corner, into its action
on `X`. -/
theorem smulTopRetractAddEquiv_symm_smul (hip : p ∘ₗ i = .id) (g : Module.End A X)
    (z : ↥((i ∘ₗ p : Module.End A M) • (⊤ : Submodule ℤ M))) :
    (smulTopRetractAddEquiv hip).symm ((cornerModuleEndAlgEquiv R hip).symm g • z) =
      g ((smulTopRetractAddEquiv hip).symm z) := by
  have hpi : ∀ y, p (i y) = y := LinearMap.congr_fun hip
  rw [smulTopRetractAddEquiv_symm_apply, IsIdempotentElem.Corner.coe_smul,
    val_cornerModuleEndAlgEquiv_symm_apply]
  simp [Module.End.smul_def, hpi]

end Corner

/-! ### Morita equivalence between endomorphism rings -/

section MoritaEquivalence

variable (R : Type*) [CommSemiring R]

/-- The restriction of scalars along an isomorphism of `R`-algebras `f : A ≃ B` carries an
`A`-module `Z` to a `B`-module `W` as soon as an additive isomorphism `Z ≃ W` turns the action of
`f.symm b` into the action of `b`. -/
theorem nonempty_ofAlgEquiv_functor_obj_iso {A B : Type u} [Ring A] [Algebra R A] [Ring B]
    [Algebra R B] (f : A ≃ₐ[R] B) {Z : ModuleCat.{u} A} {W : ModuleCat.{u} B} (g : Z ≃+ W)
    (hg : ∀ (b : B) (z : Z), g (f.symm b • z) = b • g z) :
    Nonempty ((MoritaEquivalence.ofAlgEquiv f).eqv.functor.obj Z ≅ W) :=
  let g' : (MoritaEquivalence.ofAlgEquiv f).eqv.functor.obj Z ≃ₗ[B] W :=
    { g with map_smul' := hg }
  ⟨g'.toModuleIso⟩

variable {Γ : Type*} [Ring Γ] [Algebra R Γ]
  {X Y : Type u} [AddCommGroup X] [Module Γ X] [Module R X] [IsScalarTower R Γ X]
  [AddCommGroup Y] [Module Γ Y] [Module R Y] [IsScalarTower R Γ Y]

/-- A retract `Y` of a finite power `Xᵐ` writes `id_Y` as a finite sum of maps factoring through
`X`. -/
private theorem sum_comp_eq_id_of_comp_eq_id {m : ℕ} {s : Y →ₗ[Γ] (Fin m → X)}
    {r : (Fin m → X) →ₗ[Γ] Y} (hrs : r ∘ₗ s = .id) :
    ∑ j, (r ∘ₗ LinearMap.single Γ (fun _ ↦ X) j) ∘ₗ (LinearMap.proj j ∘ₗ s) = .id := by
  refine LinearMap.ext fun y ↦ ?_
  simpa [LinearMap.sum_apply, ← map_sum] using
    (congrArg r (LinearMap.sum_single_apply (fun _ ↦ X) (s y))).trans (LinearMap.congr_fun hrs y)

/-- **Morita equivalence between the endomorphism rings of two modules in each other's additive
closure.** If each of two `Γ`-modules `X` and `Y` is a retract of a finite power of the other, a
Morita equivalence between `Module.End Γ X` and `Module.End Γ Y` carries `X` to `Y`. Both rings are
corners of `Module.End Γ (X × Y)` at full idempotents. -/
theorem exists_moritaEquivalence_moduleEnd_of_comp_eq_id {m n : ℕ}
    {s : Y →ₗ[Γ] (Fin m → X)} {r : (Fin m → X) →ₗ[Γ] Y} (hrs : r ∘ₗ s = .id)
    {s' : X →ₗ[Γ] (Fin n → Y)} {r' : (Fin n → Y) →ₗ[Γ] X} (hrs' : r' ∘ₗ s' = .id) :
    ∃ F : MoritaEquivalence R (Module.End Γ X) (Module.End Γ Y),
      Nonempty (F.eqv.functor.obj (ModuleCat.of _ X) ≅ ModuleCat.of _ Y) := by
  have hX : LinearMap.fst Γ X Y ∘ₗ LinearMap.inl Γ X Y = .id := LinearMap.fst_comp_inl ..
  have hY : LinearMap.snd Γ X Y ∘ₗ LinearMap.inr Γ X Y = .id := LinearMap.snd_comp_inr ..
  have hsum : LinearMap.inl Γ X Y ∘ₗ LinearMap.fst Γ X Y +
      LinearMap.inr Γ X Y ∘ₗ LinearMap.snd Γ X Y = .id := by
    ext <;> simp
  have hp := span_comp_eq_top_of_sum_comp_eq_id hX hsum _ _ _ (sum_comp_eq_id_of_comp_eq_id hrs)
  have hq := span_comp_eq_top_of_sum_comp_eq_id hY ((add_comm _ _).trans hsum) _ _ _
    (sum_comp_eq_id_of_comp_eq_id hrs')
  -- The `C`-module `N = X × Y`, for `C = Module.End Γ (X × Y)`, and its two pieces.
  let N := ModuleCat.of (Module.End Γ (X × Y)) (X × Y)
  let eX := isIdempotentElem_comp_of_comp_eq_id hX
  let eY := isIdempotentElem_comp_of_comp_eq_id hY
  obtain ⟨I₁⟩ := nonempty_ofAlgEquiv_functor_obj_iso R (cornerModuleEndAlgEquiv R hX).symm
    (Z := ModuleCat.of _ X) (W := eX.cornerFunctor.obj N) (smulTopRetractAddEquiv hX)
    fun c x ↦ by rw [AlgEquiv.symm_symm]; exact smulTopRetractAddEquiv_smul R hX c x
  obtain ⟨I₂⟩ := nonempty_ofAlgEquiv_functor_obj_iso R (cornerModuleEndAlgEquiv R hY)
    (Z := eY.cornerFunctor.obj N) (W := ModuleCat.of _ Y) (smulTopRetractAddEquiv hY).symm
    fun g z ↦ by exact smulTopRetractAddEquiv_symm_smul R hY g z
  -- The corner equivalences, built directly so that their functors stay `V ↦ eV`.
  let Cp : MoritaEquivalence R (Module.End Γ (X × Y)) eX.Corner :=
    ⟨eX.cornerEquivalence.{u, u} hp, inferInstanceAs (eX.cornerFunctor.{u}.Linear R)⟩
  let Cq : MoritaEquivalence R (Module.End Γ (X × Y)) eY.Corner :=
    ⟨eY.cornerEquivalence.{u, u} hq, inferInstanceAs (eY.cornerFunctor.{u}.Linear R)⟩
  refine ⟨(MoritaEquivalence.ofAlgEquiv (cornerModuleEndAlgEquiv R hX).symm).trans R
    ((Cp.symm R).trans R (Cq.trans R
      (MoritaEquivalence.ofAlgEquiv (cornerModuleEndAlgEquiv R hY)))), ⟨?_⟩⟩
  -- `X ↦ eX ↦ N ↦ eY ↦ Y`, through the unit of the first corner equivalence.
  -- The steps are kept opaque: unfolding them against the goal is slow.
  have J₁ := (Cp.symm R).eqv.functor.mapIso I₁
  have J₂ := (Cp.eqv.unitIso.app N).symm
  have J₃ := (MoritaEquivalence.ofAlgEquiv (cornerModuleEndAlgEquiv R hY)).eqv.functor.mapIso
    (Cq.eqv.functor.mapIso (J₁ ≪≫ J₂))
  exact J₃ ≪≫ I₂

end MoritaEquivalence

/-! ### Endomorphisms after restriction of scalars -/

section RestrictScalars

variable (R : Type*) [CommSemiring R] {Γ Γ' : Type*} [Ring Γ] [Ring Γ'] [Algebra R Γ]
  [Algebra R Γ'] (σ : Γ ≃ₐ[R] Γ') (W : Type u) [AddCommGroup W] [Module Γ' W] [Module R W]
  [IsScalarTower R Γ' W]

/-- **Endomorphisms after restriction of scalars along an isomorphism.** Restricting the scalars of
a `Γ'`-module `W` along an isomorphism of `R`-algebras `σ : Γ ≃ Γ'` does not change its
endomorphism algebra. -/
noncomputable def moduleEndRestrictScalarsAlgEquiv :
    Module.End Γ ((ModuleCat.restrictScalarsEquivalenceOfRingEquiv σ.toRingEquiv).functor.obj
      (ModuleCat.of Γ' W)) ≃ₐ[R] Module.End Γ' W where
  toFun φ :=
    { toFun w := φ w
      map_add' := φ.map_add
      map_smul' γ w := by
        obtain ⟨γ, rfl⟩ := σ.surjective γ
        exact φ.map_smul γ w }
  invFun ψ :=
    { toFun w := ψ w
      map_add' := ψ.map_add
      map_smul' γ w := ψ.map_smul (σ γ) w }
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl
  commutes' r := LinearMap.ext fun w ↦ by
    change σ (algebraMap R Γ r) • w = (algebraMap R (Module.End Γ' W) r) w
    rw [σ.commutes, Module.algebraMap_end_apply, algebraMap_smul]

@[simp]
theorem moduleEndRestrictScalarsAlgEquiv_apply
    (φ : Module.End Γ ((ModuleCat.restrictScalarsEquivalenceOfRingEquiv σ.toRingEquiv).functor.obj
      (ModuleCat.of Γ' W))) (w : W) :
    moduleEndRestrictScalarsAlgEquiv R σ W φ w = φ w :=
  (rfl)

@[simp]
theorem moduleEndRestrictScalarsAlgEquiv_symm_apply (ψ : Module.End Γ' W) (w : W) :
    (moduleEndRestrictScalarsAlgEquiv R σ W).symm ψ w = ψ w :=
  (rfl)

end RestrictScalars

/-! ### The correspondence -/

section Correspondence

variable (R : Type*) [CommRing R] [IsArtinianRing R] {A A' : Type u} [Ring A] [Algebra R A]
  [Module.Finite R A] [Ring A'] [Algebra R A'] [Module.Finite R A'] {M : FGModuleCat.{u} A}
  {M' : FGModuleCat.{u} A'}

/-- A finitely generated projective-injective module, with its scalars restricted along a ring
isomorphism, is still finitely generated, projective and injective. -/
private theorem finite_projective_injective_restrictScalars {Γ Γ' : Type u} [Ring Γ] [Ring Γ']
    (σ : Γ ≃+* Γ') (W : Type u) [AddCommGroup W] [Module Γ' W] [Module.Finite Γ' W]
    [Module.Projective Γ' W] [Module.Injective Γ' W] :
    Module.Finite Γ ((ModuleCat.restrictScalarsEquivalenceOfRingEquiv σ).functor.obj
        (ModuleCat.of Γ' W)) ∧
      Module.Projective Γ ((ModuleCat.restrictScalarsEquivalenceOfRingEquiv σ).functor.obj
        (ModuleCat.of Γ' W)) ∧
      Module.Injective Γ ((ModuleCat.restrictScalarsEquivalenceOfRingEquiv σ).functor.obj
        (ModuleCat.of Γ' W)) :=
  ⟨(Equivalence.finite_functor_obj_iff _ _).2 inferInstance,
    (Equivalence.projective_functor_obj_iff _ _).2 inferInstance,
    Module.injective_module_of_injective_object
      (inj := ((ModuleCat.restrictScalarsEquivalenceOfRingEquiv σ).map_injective_iff _).2
      (Module.injective_object_of_injective_module Γ' W)) _ _⟩

/-- **Additive closure through a ring isomorphism.** Let `Γ'` act faithfully and `A`-linearly on a
finitely generated `A`-module `W`, and let `σ : Γ ≃ Γ'` be a ring isomorphism. Then every finitely
generated projective and injective `Γ`-module `P` is a retract of a finite power of `W`, viewed as a
`Γ`-module through `σ`. -/
theorem exists_comp_eq_id_pi_restrictScalars {A : Type*} [Ring A] {Γ Γ' : Type*} [Ring Γ]
    [Ring Γ'] (σ : Γ ≃+* Γ') (W : Type u) [AddCommGroup W] [Module A W] [Module Γ' W]
    [SMulCommClass Γ' A W] [FaithfulSMul Γ' W] [Module.Finite A W] (P : Type u) [AddCommGroup P]
    [Module Γ P] [Module.Finite Γ P] [Module.Projective Γ P] [Module.Injective Γ P] :
    ∃ (n : ℕ) (s : P →ₗ[Γ] (Fin n → (ModuleCat.restrictScalarsEquivalenceOfRingEquiv σ).functor.obj
        (ModuleCat.of Γ' W)))
      (r : (Fin n → (ModuleCat.restrictScalarsEquivalenceOfRingEquiv σ).functor.obj
        (ModuleCat.of Γ' W)) →ₗ[Γ] P), r ∘ₗ s = .id := by
  let : Module A ((ModuleCat.restrictScalarsEquivalenceOfRingEquiv σ).functor.obj
      (ModuleCat.of Γ' W)) := inferInstanceAs (Module A W)
  have : SMulCommClass Γ A ((ModuleCat.restrictScalarsEquivalenceOfRingEquiv σ).functor.obj
      (ModuleCat.of Γ' W)) := ⟨fun γ a y ↦ smul_comm (σ γ) a (show W from y)⟩
  have : FaithfulSMul Γ ((ModuleCat.restrictScalarsEquivalenceOfRingEquiv σ).functor.obj
      (ModuleCat.of Γ' W)) := ⟨fun h ↦ σ.injective (eq_of_smul_eq_smul (α := W) h)⟩
  have : Module.Finite A ((ModuleCat.restrictScalarsEquivalenceOfRingEquiv σ).functor.obj
      (ModuleCat.of Γ' W)) := inferInstanceAs (Module.Finite A W)
  exact exists_comp_eq_id_pi_of_projective_of_injective A _ P

variable (M M') in
/-- **The Morita-Tachikawa correspondence on all modules.** If two generator-cogenerators `M` and
`M'`, of `mod A` and `mod A'`, have `R`-algebra isomorphic endomorphism rings, a Morita equivalence
between `A` and `A'` carries `M` to `M'`. -/
theorem exists_moritaEquivalence_functor_obj_iso_of_algEquiv_end
    (hM : IsGeneratorCogenerator M) (hM' : IsGeneratorCogenerator M')
    (e : Module.End A M.obj ≃ₐ[R] Module.End A' M'.obj) :
    ∃ F : MoritaEquivalence R A A', Nonempty (F.eqv.functor.obj M.obj ≅ M'.obj) := by
  obtain ⟨hs, hc⟩ := isGeneratorCogenerator_iff.1 hM
  obtain ⟨hs', hc'⟩ := isGeneratorCogenerator_iff.1 hM'
  have : Module.IsGenerator A M.obj := FGModuleCat.isGenerator_of_isSeparator hs
  have : Module.IsGenerator A' M'.obj := FGModuleCat.isGenerator_of_isSeparator hs'
  have := hc.injective_end R
  have := hc'.injective_end R
  let Y := (ModuleCat.restrictScalarsEquivalenceOfRingEquiv e.toRingEquiv).functor.obj
    (ModuleCat.of (Module.End A' M'.obj) M'.obj)
  obtain ⟨_, _, _⟩ := finite_projective_injective_restrictScalars e.toRingEquiv M'.obj
  -- Each of `M` and `Y` is a retract of a finite power of the other, over `Γ = Module.End A M`.
  obtain ⟨m, s, r, hrs⟩ := exists_comp_eq_id_pi_of_projective_of_injective
    (Γ := Module.End A M.obj) A M.obj Y
  obtain ⟨n, s', r', hrs'⟩ := exists_comp_eq_id_pi_restrictScalars (A := A') e.toRingEquiv
    M'.obj M.obj
  obtain ⟨F, ⟨I⟩⟩ := exists_moritaEquivalence_moduleEnd_of_comp_eq_id R hrs hrs'
  -- `A ≅ Module.End Γ M` and `Module.End Γ Y ≅ A'`, by the double centralizer property.
  let α := algEquivEndEndOfIsGenerator A M.obj R
  let β := (moduleEndRestrictScalarsAlgEquiv R e M'.obj).trans
    (algEquivEndEndOfIsGenerator A' M'.obj R).symm
  obtain ⟨I₁⟩ := nonempty_ofAlgEquiv_functor_obj_iso R α (Z := M.obj)
    (W := ModuleCat.of _ M.obj) (AddEquiv.refl _)
    fun φ x ↦ algEquivEndEndOfIsGenerator_symm_smul R φ x
  obtain ⟨I₂⟩ := nonempty_ofAlgEquiv_functor_obj_iso R β
    (Z := ModuleCat.of (Module.End (Module.End A M.obj) Y) Y) (W := M'.obj) (AddEquiv.refl _)
    fun a y ↦ algEquivEndEndOfIsGenerator_apply (R := A') (M := M'.obj) R a y
  exact ⟨(MoritaEquivalence.ofAlgEquiv α).trans R (F.trans R (MoritaEquivalence.ofAlgEquiv β)),
    ⟨(MoritaEquivalence.ofAlgEquiv β).eqv.functor.mapIso (F.eqv.functor.mapIso I₁ ≪≫ I) ≪≫ I₂⟩⟩

variable (M M') in
/-- **The Morita-Tachikawa correspondence, injectivity on marked pairs.** Let `M` and `M'` be
generator-cogenerators of `mod A` and `mod A'`, for Artin algebras `A` and `A'` over a commutative
Artinian ring `R`. If their endomorphism rings are isomorphic as `R`-algebras, an `R`-linear
equivalence of the categories `mod A` and `mod A'` carries `M` to `M'`. The `R`-algebra structure
on `Module.End A M.obj` comes from the action of `R` on `M` through `A`. -/
theorem exists_linear_equivalence_of_algEquiv_end (hM : IsGeneratorCogenerator M)
    (hM' : IsGeneratorCogenerator M') (e : Module.End A M.obj ≃ₐ[R] Module.End A' M'.obj) :
    ∃ F : FGModuleCat.{u} A ≌ FGModuleCat.{u} A', F.functor.Linear R ∧
      Nonempty (F.functor.obj M ≅ M') := by
  obtain ⟨F, ⟨I⟩⟩ := exists_moritaEquivalence_functor_obj_iso_of_algEquiv_end R M M' hM hM' e
  exact ⟨F.eqv.finiteModulesEquivalence, inferInstance,
    ⟨(ModuleCat.isFG A').fullyFaithfulι.preimageIso
      (eqToIso (F.eqv.finiteModulesEquivalence_functor_obj_obj M) ≪≫ I)⟩⟩

end Correspondence

end TauCeti
