/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Diffeomorph
import TauCeti.Geometry.Manifold.MFDeriv.Pi

/-!
# Diffeomorphisms of finite products of manifolds

This file constructs canonical `C^n` diffeomorphisms of finite products `∀ i, M i` of charted
spaces, modelled on `ModelWithCorners.pi I`:

* `Diffeomorph.piUnique` identifies a finite product indexed by a `Unique` type with its single
  factor `M default`, the smooth counterpart of `Equiv.piUnique` and `Homeomorph.piUnique`;
* `Diffeomorph.piSnoc` appends a last factor via `Fin.snoc`, identifying
  `(∀ i : Fin m, M i.castSucc) × M (Fin.last m)` with `∀ i : Fin (m + 1), M i`, the smooth
  counterpart of `Fin.snocEquiv` (composed with `Equiv.prodComm`);
* `Diffeomorph.mfderiv_piSnoc_apply` computes the differential of `Diffeomorph.piSnoc` on tangent
  vectors as `Fin.snoc`, using `TauCeti.mfderiv_pi`.

## Main definitions

* `Diffeomorph.piUnique`: canonical diffeomorphism `(∀ i, M i) ≃ₘ^n M default` for
  `[Unique ι]`.
* `Diffeomorph.piSnoc`: canonical diffeomorphism
  `((∀ i : Fin m, M i.castSucc) × M (Fin.last m)) ≃ₘ^n (∀ i : Fin (m + 1), M i)`.

## Main results

* `Diffeomorph.mfderiv_piSnoc_apply`: the differential of `Diffeomorph.piSnoc` acts by `Fin.snoc`
  on tangent vectors.
-/

public section

open scoped Manifold ContDiff

namespace Diffeomorph

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]

section PiUnique

variable {ι : Type*} [Fintype ι] [Unique ι]
  {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)]
  {H : ι → Type*} [∀ i, TopologicalSpace (H i)] (I : ∀ i, ModelWithCorners 𝕜 (E i) (H i))
  (M : ι → Type*) [∀ i, TopologicalSpace (M i)] [∀ i, ChartedSpace (H i) (M i)]
  (n : ℕ∞ω)

/-- A finite product of charted spaces indexed by a `Unique` type is `C^n` diffeomorphic to its
single factor `M default`. This is the smooth counterpart of `Equiv.piUnique` and
`Homeomorph.piUnique`. -/
def piUnique : (∀ i, M i) ≃ₘ^n⟮ModelWithCorners.pi I, I default⟯ M default where
  toEquiv := Equiv.piUnique M
  contMDiff_toFun := contMDiff_apply (i := default)
  contMDiff_invFun := contMDiff_pi_iff.2 fun i ↦ by
    obtain rfl := Unique.eq_default i
    simp only [Equiv.piUnique_symm_apply, uniqueElim_default]
    exact contMDiff_id

/-- `Diffeomorph.piUnique` evaluates a tuple at `default`. -/
@[simp]
theorem piUnique_apply (f : ∀ i, M i) : piUnique I M n f = f default := (rfl)

/-- The inverse of `Diffeomorph.piUnique` builds the singleton tuple via `uniqueElim`. -/
@[simp]
theorem piUnique_symm_apply (x : M default) : (piUnique I M n).symm x = uniqueElim x := (rfl)

/-- The underlying equivalence of `Diffeomorph.piUnique` is `Equiv.piUnique`. -/
@[simp]
theorem piUnique_toEquiv : (piUnique I M n).toEquiv = Equiv.piUnique M := (rfl)

end PiUnique

section PiSnoc

variable {m : ℕ}
  {E : Fin (m + 1) → Type*} [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)]
  {H : Fin (m + 1) → Type*} [∀ i, TopologicalSpace (H i)]
  (I : ∀ i, ModelWithCorners 𝕜 (E i) (H i))
  (M : Fin (m + 1) → Type*) [∀ i, TopologicalSpace (M i)] [∀ i, ChartedSpace (H i) (M i)]
  (n : ℕ∞ω)

/-- Appending a last factor via `Fin.snoc` defines a `C^n` diffeomorphism between
`(∀ i : Fin m, M i.castSucc) × M (Fin.last m)` and `∀ i : Fin (m + 1), M i`, with inverse
`g ↦ (Fin.init g, g (Fin.last m))`. -/
def piSnoc :
    ((∀ i : Fin m, M i.castSucc) × M (Fin.last m)) ≃ₘ^n⟮
      (ModelWithCorners.pi fun i : Fin m ↦ I i.castSucc).prod (I (Fin.last m)),
      ModelWithCorners.pi I⟯ (∀ i : Fin (m + 1), M i) where
  toEquiv := (Equiv.prodComm _ _).trans (Fin.snocEquiv M)
  contMDiff_toFun := contMDiff_pi_iff.2 fun i ↦ by
    induction i using Fin.lastCases with
    | last =>
      simp only [Equiv.trans_apply, Equiv.prodComm_apply, Fin.snocEquiv_apply, Fin.snoc_last]
      exact contMDiff_snd
    | cast k =>
      simp only [Equiv.trans_apply, Equiv.prodComm_apply, Fin.snocEquiv_apply, Fin.snoc_castSucc]
      exact (contMDiff_apply (i := k)).comp contMDiff_fst
  contMDiff_invFun :=
    (contMDiff_pi_iff.2 fun k ↦ contMDiff_apply (i := k.castSucc)).prodMk
      (contMDiff_apply (i := Fin.last m))

/-- `Diffeomorph.piSnoc` appends the second component to the first via `Fin.snoc`. -/
@[simp]
theorem piSnoc_apply (p : (∀ i : Fin m, M i.castSucc) × M (Fin.last m)) :
    piSnoc I M n p = Fin.snoc p.1 p.2 := (rfl)

/-- The inverse of `Diffeomorph.piSnoc` splits a tuple into its initial segment and last entry. -/
@[simp]
theorem piSnoc_symm_apply (g : ∀ i : Fin (m + 1), M i) :
    (piSnoc I M n).symm g = (Fin.init g, g (Fin.last m)) := (rfl)

/-- The underlying equivalence of `Diffeomorph.piSnoc` is `Fin.snocEquiv` composed with
`Equiv.prodComm`. -/
@[simp]
theorem piSnoc_toEquiv :
    (piSnoc I M n).toEquiv = (Equiv.prodComm _ _).trans (Fin.snocEquiv M) := (rfl)

/-- The differential of `Diffeomorph.piSnoc` acts by `Fin.snoc` on tangent vectors. -/
theorem mfderiv_piSnoc_apply (p : (∀ i : Fin m, M i.castSucc) × M (Fin.last m))
    (u : ∀ i : Fin m, E i.castSucc) (w : E (Fin.last m)) :
    mfderiv ((ModelWithCorners.pi fun i : Fin m ↦ I i.castSucc).prod (I (Fin.last m)))
      (ModelWithCorners.pi I) (piSnoc I M n) p (u, w) =
      Fin.snoc (α := E) u w := by
  let J := (ModelWithCorners.pi fun i : Fin m ↦ I i.castSucc).prod (I (Fin.last m))
  have hcomp : ∀ i : Fin (m + 1),
      MDifferentiableAt J (I i) (fun q ↦ piSnoc I M n q i) p ∧
        mfderiv J (I i) (fun q ↦ piSnoc I M n q i) p (u, w) = Fin.snoc (α := E) u w i := by
    intro i
    induction i using Fin.lastCases with
    | last =>
      have hlast : (fun q : (∀ j : Fin m, M j.castSucc) × M (Fin.last m) ↦
          piSnoc I M n q (Fin.last m)) = Prod.snd :=
        funext fun q ↦ by simp only [piSnoc_apply, Fin.snoc_last]
      refine ⟨hlast.symm ▸ mdifferentiableAt_snd, ?_⟩
      rw [Fin.snoc_last]
      exact (DFunLike.congr_fun
        (mfderiv_congr (I := J) (I' := I (Fin.last m)) hlast) (u, w)).trans
        (by rw [mfderiv_snd]; rfl)
    | cast k =>
      have hcast : (fun q : (∀ j : Fin m, M j.castSucc) × M (Fin.last m) ↦
          piSnoc I M n q k.castSucc) = (fun f ↦ f k) ∘ Prod.fst :=
        funext fun q ↦ by simp only [piSnoc_apply, Fin.snoc_castSucc, Function.comp_apply]
      have hd_apply : MDifferentiableAt (ModelWithCorners.pi fun j : Fin m ↦ I j.castSucc)
          (I k.castSucc) (fun f ↦ f k) p.1 :=
        (TauCeti.hasMFDerivAt_apply k p.1).mdifferentiableAt
      refine ⟨hcast.symm ▸ hd_apply.comp p mdifferentiableAt_fst, ?_⟩
      rw [Fin.snoc_castSucc]
      exact (DFunLike.congr_fun
        (mfderiv_congr (I := J) (I' := I k.castSucc) hcast) (u, w)).trans
        (by
          rw [mfderiv_comp p hd_apply mdifferentiableAt_fst, TauCeti.mfderiv_apply, mfderiv_fst]
          rfl)
  rw [TauCeti.mfderiv_pi fun i ↦ (hcomp i).1]
  funext i
  exact (hcomp i).2

end PiSnoc

end Diffeomorph
