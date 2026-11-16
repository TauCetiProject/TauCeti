/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Diffeomorph

/-!
# Diffeomorphisms of finite products of manifolds

Canonical `C^n` diffeomorphisms identifying finite products of charted spaces modelled on
`ModelWithCorners.pi`:

* `Diffeomorph.piUnique` and `Diffeomorph.funUnique`: a product indexed by a `Unique` finite type
  is diffeomorphic to the factor at `default`.
* `Diffeomorph.piSnoc`: adjoining the last factor `(∀ i : Fin k, M i.castSucc) × M (Fin.last k)`
  is diffeomorphic to `∀ i : Fin (k + 1), M i`.
-/

public section

open scoped Manifold ContDiff

namespace Diffeomorph

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {n : ℕ∞ω}

section PiUnique

variable {ι : Type*} [Fintype ι] [Unique ι] {E H : ι → Type*}
  [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)] [∀ i, TopologicalSpace (H i)]
  (I : ∀ i, ModelWithCorners 𝕜 (E i) (H i)) (M : ι → Type*) [∀ i, TopologicalSpace (M i)]
  [∀ i, ChartedSpace (H i) (M i)]

/-- A finite product of charted spaces indexed by a `Unique` type is `C^n` diffeomorphic to the
factor at `default`. -/
def piUnique (n : ℕ∞ω) :
    (∀ i, M i) ≃ₘ^n⟮ModelWithCorners.pi I, I default⟯ M default where
  toEquiv := Equiv.piUnique M
  contMDiff_toFun := contMDiff_apply
  contMDiff_invFun := contMDiff_pi_iff.2 fun i ↦ by
    obtain rfl := Unique.eq_default i
    simpa [Equiv.piUnique_symm_apply, Function.id_def] using contMDiff_id (I := I default)

@[simp] theorem piUnique_apply (f : ∀ i, M i) : piUnique I M n f = f default := (rfl)
@[simp] theorem piUnique_symm_apply (x : M default) :
    (piUnique I M n).symm x = uniqueElim x := (rfl)

end PiUnique

section FunUnique

variable (ι : Type*) [Fintype ι] [Unique ι] {E H : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H) (M : Type*)
  [TopologicalSpace M] [ChartedSpace H M]

/-- A finite power `ι → M` of a charted space indexed by a `Unique` type is `C^n` diffeomorphic
to `M`. -/
def funUnique (n : ℕ∞ω) : (ι → M) ≃ₘ^n⟮ModelWithCorners.pi fun _ : ι ↦ I, I⟯ M where
  toEquiv := Equiv.funUnique ι M
  contMDiff_toFun := contMDiff_apply
  contMDiff_invFun := contMDiff_pi_iff.2 fun _ ↦ contMDiff_id

@[simp] theorem funUnique_apply (f : ι → M) : funUnique ι I M n f = f default := (rfl)
@[simp] theorem funUnique_symm_apply (x : M) (i : ι) : (funUnique ι I M n).symm x i = x := (rfl)

end FunUnique

section Snoc

variable {k : ℕ} {E H : Fin (k + 1) → Type*}
  [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)] [∀ i, TopologicalSpace (H i)]
  (I : ∀ i, ModelWithCorners 𝕜 (E i) (H i)) (M : Fin (k + 1) → Type*)
  [∀ i, TopologicalSpace (M i)] [∀ i, ChartedSpace (H i) (M i)]

/-- Adjoining the last factor identifies `(∀ i : Fin k, M i.castSucc) × M (Fin.last k)` with
`∀ i : Fin (k + 1), M i` as a `C^n` diffeomorphism via `Fin.snoc`. -/
def piSnoc (n : ℕ∞ω) :
    ((∀ i : Fin k, M i.castSucc) × M (Fin.last k)) ≃ₘ^n⟮
      (ModelWithCorners.pi fun i : Fin k ↦ I i.castSucc).prod (I (Fin.last k)),
      ModelWithCorners.pi I⟯ (∀ i, M i) where
  toFun p := Fin.snoc p.1 p.2
  invFun f := (Fin.init f, f (Fin.last k))
  left_inv p := Prod.ext (Fin.init_snoc p.2 p.1) (Fin.snoc_last p.2 p.1)
  right_inv f := Fin.snoc_init_self f
  contMDiff_toFun := contMDiff_pi_iff.2 <| Fin.lastCases
    (by simpa [Fin.snoc_last] using contMDiff_snd)
    fun _ ↦ by
      simpa [Fin.snoc_castSucc, Function.comp_def] using contMDiff_apply.comp contMDiff_fst
  contMDiff_invFun := (contMDiff_pi_iff.2 fun _ ↦ contMDiff_apply).prodMk contMDiff_apply

@[simp] theorem piSnoc_apply (p : (∀ i : Fin k, M i.castSucc) × M (Fin.last k)) :
    piSnoc I M n p = Fin.snoc p.1 p.2 := (rfl)
@[simp] theorem piSnoc_symm_apply (f : ∀ i, M i) :
    (piSnoc I M n).symm f = (Fin.init f, f (Fin.last k)) := (rfl)

end Snoc

end Diffeomorph
