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
  vectors as `Fin.snoc`, using `TauCeti.mfderiv_pi`;
* `Diffeomorph.piCons` prepends a first factor via `Fin.cons`, identifying
  `M 0 × (∀ i : Fin m, M i.succ)` with `∀ i : Fin (m + 1), M i`, the smooth counterpart of
  `Fin.consEquiv`; its inverse `g ↦ (g 0, Fin.tail g)` splits off the first factor, and its
  differential acts on tangent vectors by `Fin.cons` (`Diffeomorph.mfderiv_piCons_apply`);
* `Diffeomorph.piAddCases` concatenates two blocks of factors via `Fin.addCases`, identifying
  `(∀ i : Fin m, M (Fin.castAdd k i)) × (∀ j : Fin k, M (Fin.natAdd m j))` with
  `∀ i : Fin (m + k), M i`, the dependent smooth counterpart of `Fin.appendEquiv`; its differential
  acts on tangent vectors by `Fin.addCases` (`Diffeomorph.mfderiv_piAddCases_apply`).

## Main definitions

* `Diffeomorph.piUnique`: canonical diffeomorphism `(∀ i, M i) ≃ₘ^n M default` for
  `[Unique ι]`.
* `Diffeomorph.piSnoc`: canonical diffeomorphism
  `((∀ i : Fin m, M i.castSucc) × M (Fin.last m)) ≃ₘ^n (∀ i : Fin (m + 1), M i)`.
* `Diffeomorph.piCons`: canonical diffeomorphism
  `(M 0 × ∀ i : Fin m, M i.succ) ≃ₘ^n (∀ i : Fin (m + 1), M i)`.
* `Diffeomorph.piAddCases`: canonical diffeomorphism
  `((∀ i : Fin m, M (Fin.castAdd k i)) × (∀ j : Fin k, M (Fin.natAdd m j))) ≃ₘ^n
  (∀ i : Fin (m + k), M i)`.

## Main results

* `Diffeomorph.mfderiv_piSnoc_apply`: the differential of `Diffeomorph.piSnoc` acts by `Fin.snoc`
  on tangent vectors.
* `Diffeomorph.mfderiv_piCons_apply`: the differential of `Diffeomorph.piCons` acts by `Fin.cons`
  on tangent vectors.
* `Diffeomorph.mfderiv_piAddCases_apply`: the differential of `Diffeomorph.piAddCases` acts by
  `Fin.addCases` on tangent vectors.
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
      have h := hasMFDerivAt_snd (I := ModelWithCorners.pi fun i : Fin m ↦ I i.castSucc)
        (I' := I (Fin.last m)) p
      rw [show (fun q ↦ piSnoc I M n q (Fin.last m)) = Prod.snd from
        funext fun q ↦ by simp, Fin.snoc_last]
      exact ⟨h.mdifferentiableAt, DFunLike.congr_fun h.mfderiv (u, w)⟩
    | cast k =>
      have h := (TauCeti.hasMFDerivAt_apply (I := fun i : Fin m ↦ I i.castSucc) k p.1).comp p
        (hasMFDerivAt_fst (I' := I (Fin.last m)) p)
      rw [show (fun q ↦ piSnoc I M n q k.castSucc) = (fun f ↦ f k) ∘ Prod.fst from
        funext fun q ↦ by simp, Fin.snoc_castSucc]
      exact ⟨h.mdifferentiableAt, DFunLike.congr_fun h.mfderiv (u, w)⟩
  rw [TauCeti.mfderiv_pi fun i ↦ (hcomp i).1]
  funext i
  exact (hcomp i).2

end PiSnoc

section PiCons

variable {m : ℕ}
  {E : Fin (m + 1) → Type*} [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)]
  {H : Fin (m + 1) → Type*} [∀ i, TopologicalSpace (H i)]
  (I : ∀ i, ModelWithCorners 𝕜 (E i) (H i))
  (M : Fin (m + 1) → Type*) [∀ i, TopologicalSpace (M i)] [∀ i, ChartedSpace (H i) (M i)]
  (n : ℕ∞ω)

/-- Prepending a first factor via `Fin.cons` defines a `C^n` diffeomorphism between
`M 0 × (∀ i : Fin m, M i.succ)` and `∀ i : Fin (m + 1), M i`, with inverse
`g ↦ (g 0, Fin.tail g)`, the association map splitting off the first factor. This is the smooth
counterpart of `Fin.consEquiv`. -/
def piCons :
    (M 0 × ∀ i : Fin m, M i.succ) ≃ₘ^n⟮
      (I 0).prod (ModelWithCorners.pi fun i : Fin m ↦ I i.succ),
      ModelWithCorners.pi I⟯ (∀ i : Fin (m + 1), M i) where
  toEquiv := Fin.consEquiv M
  contMDiff_toFun := contMDiff_pi_iff.2 fun i ↦ by
    induction i using Fin.cases with
    | zero =>
      simp only [Fin.consEquiv_apply, Fin.cons_zero]
      exact contMDiff_fst
    | succ k =>
      simp only [Fin.consEquiv_apply, Fin.cons_succ]
      exact (contMDiff_apply (i := k)).comp contMDiff_snd
  contMDiff_invFun :=
    (contMDiff_apply (i := 0)).prodMk (contMDiff_pi_iff.2 fun k ↦ contMDiff_apply (i := k.succ))

/-- `Diffeomorph.piCons` prepends the first component to the second via `Fin.cons`. -/
@[simp]
theorem piCons_apply (p : M 0 × ∀ i : Fin m, M i.succ) :
    piCons I M n p = Fin.cons p.1 p.2 := (rfl)

/-- The inverse of `Diffeomorph.piCons` splits a tuple into its first entry and its tail. -/
@[simp]
theorem piCons_symm_apply (g : ∀ i : Fin (m + 1), M i) :
    (piCons I M n).symm g = (g 0, Fin.tail g) := (rfl)

/-- The underlying equivalence of `Diffeomorph.piCons` is `Fin.consEquiv`. -/
@[simp]
theorem piCons_toEquiv : (piCons I M n).toEquiv = Fin.consEquiv M := (rfl)

/-- The differential of `Diffeomorph.piCons` acts by `Fin.cons` on tangent vectors. -/
theorem mfderiv_piCons_apply (p : M 0 × ∀ i : Fin m, M i.succ) (u : E 0)
    (w : ∀ i : Fin m, E i.succ) :
    mfderiv ((I 0).prod (ModelWithCorners.pi fun i : Fin m ↦ I i.succ))
      (ModelWithCorners.pi I) (piCons I M n) p (u, w) =
      Fin.cons (α := E) u w := by
  let J := (I 0).prod (ModelWithCorners.pi fun i : Fin m ↦ I i.succ)
  have hcomp : ∀ i : Fin (m + 1),
      MDifferentiableAt J (I i) (fun q ↦ piCons I M n q i) p ∧
        mfderiv J (I i) (fun q ↦ piCons I M n q i) p (u, w) = Fin.cons (α := E) u w i := by
    intro i
    induction i using Fin.cases with
    | zero =>
      have h := hasMFDerivAt_fst (I := I 0)
        (I' := ModelWithCorners.pi fun i : Fin m ↦ I i.succ) p
      rw [show (fun q ↦ piCons I M n q 0) = Prod.fst from funext fun q ↦ by simp, Fin.cons_zero]
      exact ⟨h.mdifferentiableAt, DFunLike.congr_fun h.mfderiv (u, w)⟩
    | succ k =>
      have h := (TauCeti.hasMFDerivAt_apply (I := fun i : Fin m ↦ I i.succ) k p.2).comp p
        (hasMFDerivAt_snd (I := I 0) p)
      rw [show (fun q ↦ piCons I M n q k.succ) = (fun f ↦ f k) ∘ Prod.snd from
        funext fun q ↦ by simp, Fin.cons_succ]
      exact ⟨h.mdifferentiableAt, DFunLike.congr_fun h.mfderiv (u, w)⟩
  rw [TauCeti.mfderiv_pi fun i ↦ (hcomp i).1]
  funext i
  exact (hcomp i).2

end PiCons

section PiAddCases

variable {m k : ℕ}
  {E : Fin (m + k) → Type*} [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)]
  {H : Fin (m + k) → Type*} [∀ i, TopologicalSpace (H i)]
  (I : ∀ i, ModelWithCorners 𝕜 (E i) (H i))
  (M : Fin (m + k) → Type*) [∀ i, TopologicalSpace (M i)] [∀ i, ChartedSpace (H i) (M i)]
  (n : ℕ∞ω)

/-- Concatenating two blocks of factors via `Fin.addCases` defines a `C^n` diffeomorphism between
`(∀ i : Fin m, M (Fin.castAdd k i)) × (∀ j : Fin k, M (Fin.natAdd m j))` and
`∀ i : Fin (m + k), M i`, with inverse `g ↦ (g ∘ Fin.castAdd k, g ∘ Fin.natAdd m)`. This is the
dependent smooth counterpart of `Fin.appendEquiv`. -/
def piAddCases :
    ((∀ i : Fin m, M (Fin.castAdd k i)) × (∀ j : Fin k, M (Fin.natAdd m j))) ≃ₘ^n⟮
      (ModelWithCorners.pi fun i : Fin m ↦ I (Fin.castAdd k i)).prod
        (ModelWithCorners.pi fun j : Fin k ↦ I (Fin.natAdd m j)),
      ModelWithCorners.pi I⟯ (∀ i : Fin (m + k), M i) where
  toFun p := Fin.addCases (motive := M) p.1 p.2
  invFun g := (fun i ↦ g (Fin.castAdd k i), fun j ↦ g (Fin.natAdd m j))
  left_inv p := by simp
  right_inv g := funext fun i ↦ by
    induction i using Fin.addCases <;> simp
  contMDiff_toFun := contMDiff_pi_iff.2 fun i ↦ by
    induction i using Fin.addCases with
    | left i =>
      simp only [Equiv.coe_fn_mk, Fin.addCases_left]
      exact (contMDiff_apply (i := i)).comp contMDiff_fst
    | right j =>
      simp only [Equiv.coe_fn_mk, Fin.addCases_right]
      exact (contMDiff_apply (i := j)).comp contMDiff_snd
  contMDiff_invFun :=
    (contMDiff_pi_iff.2 fun i ↦ contMDiff_apply (i := Fin.castAdd k i)).prodMk
      (contMDiff_pi_iff.2 fun j ↦ contMDiff_apply (i := Fin.natAdd m j))

/-- `Diffeomorph.piAddCases` concatenates its two components via `Fin.addCases`. -/
@[simp]
theorem piAddCases_apply
    (p : (∀ i : Fin m, M (Fin.castAdd k i)) × (∀ j : Fin k, M (Fin.natAdd m j))) :
    piAddCases I M n p = Fin.addCases (motive := M) p.1 p.2 := (rfl)

/-- The inverse of `Diffeomorph.piAddCases` splits a tuple into its first `m` and its last `k`
entries. -/
@[simp]
theorem piAddCases_symm_apply (g : ∀ i : Fin (m + k), M i) :
    (piAddCases I M n).symm g = (fun i ↦ g (Fin.castAdd k i), fun j ↦ g (Fin.natAdd m j)) := (rfl)

/-- The differential of `Diffeomorph.piAddCases` acts by `Fin.addCases` on tangent vectors. -/
theorem mfderiv_piAddCases_apply
    (p : (∀ i : Fin m, M (Fin.castAdd k i)) × (∀ j : Fin k, M (Fin.natAdd m j)))
    (u : ∀ i : Fin m, E (Fin.castAdd k i)) (w : ∀ j : Fin k, E (Fin.natAdd m j)) :
    mfderiv ((ModelWithCorners.pi fun i : Fin m ↦ I (Fin.castAdd k i)).prod
        (ModelWithCorners.pi fun j : Fin k ↦ I (Fin.natAdd m j)))
      (ModelWithCorners.pi I) (piAddCases I M n) p (u, w) =
      Fin.addCases (motive := E) u w := by
  let J := (ModelWithCorners.pi fun i : Fin m ↦ I (Fin.castAdd k i)).prod
    (ModelWithCorners.pi fun j : Fin k ↦ I (Fin.natAdd m j))
  have hcomp : ∀ i : Fin (m + k),
      MDifferentiableAt J (I i) (fun q ↦ piAddCases I M n q i) p ∧
        mfderiv J (I i) (fun q ↦ piAddCases I M n q i) p (u, w) =
          Fin.addCases (motive := E) u w i := by
    intro i
    induction i using Fin.addCases with
    | left i =>
      have h := (TauCeti.hasMFDerivAt_apply (I := fun i : Fin m ↦ I (Fin.castAdd k i)) i p.1).comp
        p (hasMFDerivAt_fst (I' := ModelWithCorners.pi fun j : Fin k ↦ I (Fin.natAdd m j)) p)
      rw [show (fun q ↦ piAddCases I M n q (Fin.castAdd k i)) = (fun f ↦ f i) ∘ Prod.fst from
        funext fun q ↦ by simp, Fin.addCases_left]
      exact ⟨h.mdifferentiableAt, DFunLike.congr_fun h.mfderiv (u, w)⟩
    | right j =>
      have h := (TauCeti.hasMFDerivAt_apply (I := fun j : Fin k ↦ I (Fin.natAdd m j)) j p.2).comp
        p (hasMFDerivAt_snd (I := ModelWithCorners.pi fun i : Fin m ↦ I (Fin.castAdd k i)) p)
      rw [show (fun q ↦ piAddCases I M n q (Fin.natAdd m j)) = (fun f ↦ f j) ∘ Prod.snd from
        funext fun q ↦ by simp, Fin.addCases_right]
      exact ⟨h.mdifferentiableAt, DFunLike.congr_fun h.mfderiv (u, w)⟩
  rw [TauCeti.mfderiv_pi fun i ↦ (hcomp i).1]
  funext i
  exact (hcomp i).2

end PiAddCases

end Diffeomorph
