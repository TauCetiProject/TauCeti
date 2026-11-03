/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.IsTensorProduct
public import TauCeti.LinearAlgebra.TensorProduct.Torsion
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import TauCeti.Algebra.Module.Torsion.PrimaryComponent
import TauCeti.RingTheory.Ideal.Quotient.Operations

/-!
# Ideal-power torsion modules under formal glueing base change

Let `R → S` be a flat ring map and `I` an ideal of `R` such that `R ⧸ I → S ⧸ IS` is bijective.
The typical example is the `I`-adic completion of a Noetherian ring. `I`-power torsion modules
do not change under base change to `S`: such a module `M` is identified with `S ⊗[R] M` by
`m ↦ 1 ⊗ m`. This is the first input of formal glueing (Stacks, Section 15.91):
modules over `R` are determined by their base change to `S` together with their restrictions to
the open complement of `V(I)`, and the comparison of the two descriptions only involves
`I`-power torsion modules.

Write `Γ_I(M)` for the `I`-primary component `Ideal.primaryComponent M I`, the submodule of
elements killed by a power of `I`, and `IS` for the extended ideal `I.map (algebraMap R S)`.

## Main results

* `TauCeti.tensorProduct_mk_bijective_of_primaryComponent_eq_top`: if `M` is `I`-power torsion,
  then `M → S ⊗[R] M`, `m ↦ 1 ⊗ m`, is bijective.
* `TauCeti.primaryComponentEquivTensorProduct`: for finitely generated `I`, the map `m ↦ 1 ⊗ m`
  identifies `Γ_I(M)` with `Γ_{IS}(S ⊗[R] M)` for every `R`-module `M`.
* `TauCeti.baseChangeHom_bijective_of_primaryComponent_eq_top_right` and
  `TauCeti.baseChangeHom_bijective_of_primaryComponent_eq_top_left`: base change
  `Hom_R(M, N) → Hom_S(S ⊗ M, S ⊗ N)` is bijective if `N`, or (for finitely generated `I`) `M`,
  is `I`-power torsion.
* `TauCeti.isBaseChange_of_primaryComponent_eq_top`: an `IS`-power torsion `S`-module is the base
  change of its underlying `R`-module.

Together with `TauCeti.primaryComponent_map_tensorProduct_eq_top`, base change of an `I`-power
torsion module is `IS`-power torsion, these say that base change is an equivalence from
`I`-power torsion `R`-modules to `IS`-power torsion `S`-modules.

Along the way, `TauCeti.primaryComponent_map_tensorProduct_eq_bot` shows that flat base change
of a module without `I`-power torsion has no `IS`-power torsion, for finitely generated `I`.

## References

* [Stacks Project, Lemma 15.91.2](https://stacks.math.columbia.edu/tag/05E9), the implication
  (2) ⇒ (1).
* [Stacks Project, Lemma 15.91.3](https://stacks.math.columbia.edu/tag/05EC).
-/

public section

open TensorProduct Submodule Function

namespace TauCeti

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] {I : Ideal R}
  {M : Type*} [AddCommGroup M] [Module R M]

variable [Module.Flat R S]
  (hI : Bijective (Ideal.quotientMap (I.map (algebraMap R S)) (algebraMap R S) Ideal.le_comap_map))
include hI

omit [Module.Flat R S] in
/-- An `R`-module killed by `I` is identified with its base change to `S`: the inverse sends
`s ⊗ m` to `r • m` for any `r` congruent to `s` modulo `IS`. -/
private theorem tensorProduct_mk_bijective_of_isTorsionBySet
    (hM : Module.IsTorsionBySet R M I) : Bijective (TensorProduct.mk R S M 1) := by
  let := hM.module
  let e := RingEquiv.ofBijective _ hI
  let φ : S →+* R ⧸ I := e.symm.toRingHom.comp (Ideal.Quotient.mk _)
  have hφ (r : R) : φ (algebraMap R S r) = Ideal.Quotient.mk I r :=
    e.symm_apply_eq.mpr (by simp [e])
  have hsmul (r : R) (m : M) : Ideal.Quotient.mk I r • m = r • m :=
    Module.IsTorsionBySet.mk_smul hM r m
  let β : S →ₗ[R] M →ₗ[R] M := LinearMap.mk₂ R (fun s m ↦ φ s • m)
    (fun _ _ _ ↦ by rw [map_add, add_smul])
    (fun r s m ↦ by rw [Algebra.smul_def, map_mul, hφ, mul_smul, hsmul])
    (fun _ _ _ ↦ smul_add _ _ _)
    (fun r s m ↦ by rw [← hsmul, ← hsmul r, smul_smul, smul_smul, mul_comm])
  refine ⟨LeftInverse.injective (g := TensorProduct.lift β) fun m ↦ by simp [β], fun x ↦ ?_⟩
  induction x using TensorProduct.inductionOn with
  | tmul s m =>
    obtain ⟨r, hr⟩ := Ideal.exists_sub_mem_of_surjective_quotientMap hI.2 s
    have hm : m ∈ torsionBySet R M I := (mem_torsionBySet_iff _ _).mpr fun a ↦ @hM m a
    have h := (Ideal.mem_torsionOf_iff _ _).mp (map_le_torsionOf_one_tmul (S := S) hm hr)
    rw [smul_tmul', smul_eq_mul, mul_one, sub_tmul, sub_eq_zero] at h
    refine ⟨r • m, ?_⟩
    rw [mk_apply, ← smul_tmul, Algebra.smul_def, mul_one, h]
  | add x y hx hy =>
    obtain ⟨a, rfl⟩ := hx
    obtain ⟨b, rfl⟩ := hy
    exact ⟨a + b, map_add _ _ _⟩

/-- If `R → S` is flat and `R ⧸ I → S ⧸ IS` is bijective, then for every `R`-module `M` killed
by `I ^ n` the map `M → S ⊗[R] M`, `m ↦ 1 ⊗ m`, is bijective. -/
private theorem tensorProduct_mk_bijective_of_isTorsionBySet_pow (n : ℕ) :
    ∀ (M : Type*) [AddCommGroup M] [Module R M], Module.IsTorsionBySet R M ↑(I ^ n) →
      Bijective (TensorProduct.mk R S M 1) := by
  -- Induct on `n` along `0 → M[I] → M → M ⧸ M[I] → 0`.
  induction n with
  | zero =>
    intro M _ _ hM
    refine tensorProduct_mk_bijective_of_isTorsionBySet hI fun m a ↦ ?_
    exact @hM m ⟨a, by simp⟩
  | succ n ih =>
    intro M _ _ hM
    let N := torsionBySet R M I
    have hN := tensorProduct_mk_bijective_of_isTorsionBySet (M := N) hI
      (torsionBySet_isTorsionBySet _)
    have hQ := ih (M ⧸ N) fun q a ↦ by
      obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ q
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, mem_torsionBySet_iff]
      intro i
      rw [smul_smul]
      exact @hM m ⟨_, by rw [pow_succ']; exact Ideal.mul_mem_mul i.2 a.2⟩
    refine ⟨(injective_iff_map_eq_zero _).mpr fun m hm ↦ ?_, fun y ↦ ?_⟩
    · have hmN : m ∈ N := by
        rw [← Submodule.Quotient.mk_eq_zero]
        refine (injective_iff_map_eq_zero _).mp hQ.1 _ ?_
        simpa using congr(N.mkQ.lTensor S $hm)
      have : (1 : S) ⊗ₜ[R] (⟨m, hmN⟩ : N) = 0 :=
        Module.Flat.lTensor_preserves_injective_linearMap N.subtype N.injective_subtype
          (by simpa using hm)
      simpa using congr(Subtype.val $((injective_iff_map_eq_zero _).mp hN.1 _ this))
    · obtain ⟨q, hq⟩ := hQ.2 (N.mkQ.lTensor S y)
      obtain ⟨m, rfl⟩ := N.mkQ_surjective q
      obtain ⟨z, hz⟩ := (lTensor_exact S (LinearMap.exact_subtype_mkQ N) N.mkQ_surjective
        (y - 1 ⊗ₜ m)).mp (by simp [map_sub, ← hq])
      obtain ⟨p, rfl⟩ := hN.2 z
      refine ⟨m + p, ?_⟩
      simp only [mk_apply, LinearMap.lTensor_tmul, subtype_apply] at hz ⊢
      rw [tmul_add, hz, add_sub_cancel]

/-- **`I`-power torsion modules are unchanged by base change.** If `R → S` is flat and
`R ⧸ I → S ⧸ IS` is bijective, then for every `I`-power torsion `R`-module `M` the map
`M → S ⊗[R] M`, `m ↦ 1 ⊗ m`, is bijective. -/
@[stacks 05E9 "(2) ⇒ (1)"]
theorem tensorProduct_mk_bijective_of_primaryComponent_eq_top
    (hM : I.primaryComponent M = ⊤) : Bijective (TensorProduct.mk R S M 1) := by
  have hmem (m : M) : ∃ n, m ∈ torsionBySet R M ↑(I ^ n) :=
    (Ideal.primaryComponent_mem _ _ _).mp (hM ▸ mem_top)
  have hb (n : ℕ) := tensorProduct_mk_bijective_of_isTorsionBySet_pow hI n
    (torsionBySet R M ↑(I ^ n)) (torsionBySet_isTorsionBySet _)
  refine ⟨(injective_iff_map_eq_zero _).mpr fun m hm ↦ ?_, fun y ↦ ?_⟩
  · obtain ⟨n, hn⟩ := hmem m
    have : (1 : S) ⊗ₜ[R] (⟨m, hn⟩ : torsionBySet R M ↑(I ^ n)) = 0 :=
      Module.Flat.lTensor_preserves_injective_linearMap _ (injective_subtype _)
        (by simpa using hm)
    simpa using congr(Subtype.val $((injective_iff_map_eq_zero _).mp (hb n).1 _ this))
  · induction y using TensorProduct.inductionOn with
    | tmul s m =>
      obtain ⟨n, hn⟩ := hmem m
      obtain ⟨p, hp⟩ := (hb n).2 (s ⊗ₜ ⟨m, hn⟩)
      exact ⟨p, by simpa using congr((torsionBySet R M ↑(I ^ n)).subtype.lTensor S $hp)⟩
    | add x y hx hy =>
      obtain ⟨a, rfl⟩ := hx
      obtain ⟨b, rfl⟩ := hy
      exact ⟨a + b, map_add _ _ _⟩

omit hI in
/-- The restriction of `m ↦ 1 ⊗ m` to `I`-power torsion elements, as a map into the
`IS`-power torsion of `S ⊗[R] M`. -/
private noncomputable def primaryComponentMap :
    I.primaryComponent M →ₗ[R]
      ((I.map (algebraMap R S)).primaryComponent (S ⊗[R] M)).restrictScalars R :=
  ((TensorProduct.mk R S M 1).domRestrict _).codRestrict _ fun m ↦
    one_tmul_mem_primaryComponent_map m.2

omit [Module.Flat R S] hI in
private theorem coe_primaryComponentMap_apply (m : I.primaryComponent M) :
    (primaryComponentMap (S := S) m : S ⊗[R] M) = 1 ⊗ₜ (m : M) :=
  rfl

private theorem primaryComponentMap_bijective (hIfg : I.FG) :
    Bijective (primaryComponentMap (S := S) (I := I) (M := M)) := by
  let P := I.primaryComponent M
  have hP := tensorProduct_mk_bijective_of_primaryComponent_eq_top (M := P) hI
    (Ideal.primaryComponent_primaryComponent_eq_top I)
  refine ⟨(injective_iff_map_eq_zero _).mpr fun m hm ↦ ?_, fun ⟨y, hy⟩ ↦ ?_⟩
  · refine (injective_iff_map_eq_zero _).mp hP.1 _
      (Module.Flat.lTensor_preserves_injective_linearMap P.subtype P.injective_subtype ?_)
    simpa [coe_primaryComponentMap_apply] using congr(Subtype.val $hm)
  · -- The image of `y` in `S ⊗ (M ⧸ P)` is `IS`-power torsion, hence zero.
    have hQ := primaryComponent_map_tensorProduct_eq_bot (S := S)
      (M := M ⧸ P) hIfg (Ideal.primaryComponent_quotient_primaryComponent hIfg)
    have hy' : P.mkQ.lTensor S y = 0 := by
      have := Ideal.primaryComponent_map_mem _ (P.mkQ.baseChange S) ⟨y, hy⟩
      rwa [hQ, mem_bot] at this
    obtain ⟨z, rfl⟩ := (lTensor_exact S (LinearMap.exact_subtype_mkQ P) P.mkQ_surjective y).mp hy'
    obtain ⟨p, rfl⟩ := hP.2 z
    exact ⟨p, Subtype.ext (by simp [coe_primaryComponentMap_apply])⟩

/-- For finitely generated `I`, the map `m ↦ 1 ⊗ m` identifies the `I`-power torsion of an
`R`-module `M` with the `IS`-power torsion of `S ⊗[R] M`. -/
@[stacks 05EC "(1)"]
noncomputable def primaryComponentEquivTensorProduct (hIfg : I.FG) :
    I.primaryComponent M ≃ₗ[R]
      ((I.map (algebraMap R S)).primaryComponent (S ⊗[R] M)).restrictScalars R :=
  .ofBijective primaryComponentMap (primaryComponentMap_bijective hI hIfg)

/-- `primaryComponentEquivTensorProduct` is `m ↦ 1 ⊗ m`. -/
@[simp]
theorem coe_primaryComponentEquivTensorProduct_apply (hIfg : I.FG) (m : I.primaryComponent M) :
    (primaryComponentEquivTensorProduct hI hIfg m : S ⊗[R] M) = 1 ⊗ₜ (m : M) := by
  rw [primaryComponentEquivTensorProduct, LinearEquiv.ofBijective_apply,
    coe_primaryComponentMap_apply]

/-- Base change `Hom_R(M, N) → Hom_S(S ⊗ M, S ⊗ N)` is bijective when `N` is `I`-power
torsion. -/
@[stacks 05EC "(2), for `N` torsion"]
theorem baseChangeHom_bijective_of_primaryComponent_eq_top_right {N : Type*} [AddCommGroup N]
    [Module R N] (hN : I.primaryComponent N = ⊤) :
    Bijective (LinearMap.baseChangeHom R S M N) := by
  have hb := tensorProduct_mk_bijective_of_primaryComponent_eq_top hI (S := S) hN
  refine ⟨(injective_iff_map_eq_zero _).mpr fun f hf ↦ LinearMap.ext fun m ↦ ?_, fun g ↦ ?_⟩
  · refine (injective_iff_map_eq_zero _).mp hb.1 _ ?_
    simpa using LinearMap.congr_fun hf (1 ⊗ₜ m)
  · let e := LinearEquiv.ofBijective _ hb
    refine ⟨e.symm.toLinearMap ∘ₗ g.restrictScalars R ∘ₗ TensorProduct.mk R S M 1, ?_⟩
    ext m
    have h := e.apply_symm_apply (g (1 ⊗ₜ m))
    rw [LinearEquiv.ofBijective_apply, mk_apply] at h
    simpa using h

/-- Base change `Hom_R(M, N) → Hom_S(S ⊗ M, S ⊗ N)` is bijective when `M` is `I`-power
torsion and `I` is finitely generated. -/
@[stacks 05EC "(2), for `M` torsion"]
theorem baseChangeHom_bijective_of_primaryComponent_eq_top_left (hIfg : I.FG) {N : Type*}
    [AddCommGroup N] [Module R N] (hM : I.primaryComponent M = ⊤) :
    Bijective (LinearMap.baseChangeHom R S M N) := by
  let e := primaryComponentEquivTensorProduct (S := S) (M := N) hI hIfg
  have hf (f : M →ₗ[R] N) (m : M) : f m ∈ I.primaryComponent N :=
    Ideal.primaryComponent_map_mem _ f ⟨m, hM ▸ mem_top⟩
  have hg (g : S ⊗[R] M →ₗ[S] S ⊗[R] N) (m : M) :
      g (1 ⊗ₜ m) ∈ (I.map (algebraMap R S)).primaryComponent (S ⊗[R] N) :=
    Ideal.primaryComponent_map_mem _ g ⟨_, one_tmul_mem_primaryComponent_map (hM ▸ mem_top)⟩
  refine ⟨(injective_iff_map_eq_zero _).mpr fun f hf' ↦ LinearMap.ext fun m ↦ ?_, fun g ↦ ?_⟩
  · have : e ⟨f m, hf f m⟩ = 0 := Subtype.ext <| by
      rw [coe_primaryComponentEquivTensorProduct_apply]
      simpa using LinearMap.congr_fun hf' (1 ⊗ₜ m)
    simpa using this
  · refine ⟨(I.primaryComponent N).subtype ∘ₗ e.symm.toLinearMap ∘ₗ
      (g.restrictScalars R ∘ₗ TensorProduct.mk R S M 1).codRestrict _ (hg g), ?_⟩
    ext m
    have h := congr(Subtype.val $(e.apply_symm_apply ⟨g (1 ⊗ₜ m), hg g m⟩))
    rw [coe_primaryComponentEquivTensorProduct_apply] at h
    -- The goal is `h` with the codomain restriction applied to `m` unfolded.
    exact h

/-- An `S`-module that is `IS`-power torsion is the base change of its underlying `R`-module:
the multiplication map `S ⊗[R] N → N` is bijective. -/
@[stacks 05EC "(3), essential surjectivity"]
theorem isBaseChange_of_primaryComponent_eq_top {N : Type*} [AddCommGroup N] [Module R N]
    [Module S N] [IsScalarTower R S N]
    (hN : (I.map (algebraMap R S)).primaryComponent N = ⊤) :
    IsBaseChange S ((LinearMap.id : N →ₗ[S] N).restrictScalars R) := by
  -- As an `R`-module, `N` is `I`-power torsion.
  have hN' : I.primaryComponent N = ⊤ := by
    refine eq_top_iff.mpr fun x _ ↦ ?_
    obtain ⟨n, hn⟩ := (Ideal.primaryComponent_mem _ _ _).mp (hN ▸ mem_top : x ∈ _)
    refine (Ideal.primaryComponent_mem _ _ _).mpr ⟨n, (mem_torsionBySet_iff _ _).mpr fun a ↦ ?_⟩
    rw [← algebraMap_smul S]
    exact (mem_torsionBySet_iff _ _).mp hn
      ⟨_, Ideal.map_pow (algebraMap R S) I n ▸ Ideal.mem_map_of_mem _ a.2⟩
  have hb := tensorProduct_mk_bijective_of_primaryComponent_eq_top hI (S := S) hN'
  let l := ((LinearMap.id : N →ₗ[S] N).restrictScalars R).liftBaseChange S
  have hl (n : N) : l (1 ⊗ₜ n) = n := by simp [l]
  have hlb : Bijective l := by
    refine ⟨fun x y hxy ↦ ?_, fun n ↦ ⟨_, hl n⟩⟩
    obtain ⟨a, rfl⟩ := hb.2 x
    obtain ⟨b, rfl⟩ := hb.2 y
    simp only [mk_apply, hl] at hxy
    rw [hxy]
  exact IsBaseChange.of_equiv (.ofBijective l hlb) fun n ↦ hl n

end TauCeti
