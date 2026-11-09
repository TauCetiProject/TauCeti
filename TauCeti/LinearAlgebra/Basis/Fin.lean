/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Alternating.Curry
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# A vector followed by a basis of a hyperplane

Let `V` be a vector space of dimension `k + 1`, `W` a subspace and `b` a basis of `W` indexed by
`Fin k`. For any `v ∉ W`, the vectors `v, b 0, …, b (k - 1)` form a basis of `V`
(`Module.Basis.mkFinConsOfNotMem`). This is Mathlib's `Module.Basis.mkFinCons` for vector spaces,
where the dimension count replaces the hypothesis that `v` and `W` together span `V`.

Over any commutative ring, if a basis `c` of `V` is `v` followed by a basis `b` of `W`, then
`u ↦ c.det (v, u)` is the determinant with respect to `b`
(`Module.Basis.det_finCons_eq_det`). In particular, `v` followed by a basis of `W` has nonzero
determinant with respect to every basis of `V` (`Module.Basis.det_finCons_ne_zero`).

Reindexing a basis along `finCongr` and then precomposing with a `Fin.cast` is the original basis
precomposed with the composite cast (`Module.Basis.reindex_finCongr_comp_cast`). This identifies
the families on which top-degree forms are evaluated when the dimension is written in different
but equal ways.

## Main definitions

* `Module.Basis.mkFinConsOfNotMem`: the basis `v, b 0, …, b (k - 1)` of `V`.

## Main results

* `Module.Basis.det_finCons_eq_det`: the determinant of `v` followed by a family in `W`, with
  respect to a basis beginning with `v` and continuing with `b`, is its determinant with respect
  to `b`.
* `Module.Basis.det_finCons_ne_zero`: `v` followed by a basis of `W` has nonzero determinant.
* `Module.Basis.exists_repr_zero_ne_zero`: a nonzero vector has nonzero zeroth coordinate in some
  basis indexed by `Fin (k + 1)`.
* `Module.Basis.exists_basis_finCons_of_apply_eq_one`: if a linear functional takes the value one
  on `v`, then `v` followed by a basis of its kernel is a basis.
* `Module.Basis.reindex_finCongr_comp_cast`: a basis reindexed along `finCongr` and precomposed
  with a `Fin.cast` is the original basis precomposed with a `Fin.cast`.
-/

public section

noncomputable section

namespace Module.Basis

/-- A basis reindexed along `finCongr h` and precomposed with `Fin.cast h'` is the original basis
precomposed with the composite cast. -/
theorem reindex_finCongr_comp_cast {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    {k m m' : ℕ} (b : Basis (Fin m) R M) (h : m = m') (h' : k = m') :
    ⇑(b.reindex (finCongr h)) ∘ Fin.cast h' = ⇑b ∘ Fin.cast (h'.trans h.symm) := by
  funext i
  simp

section CommRing

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V] {k : ℕ} {W : Submodule R V}
  {v : V}

/-- For a basis `c` of `V` beginning with `v` and continuing with a basis `b` of `W`, and a family
`u` in `W`, the determinant of `v, u 0, …, u (k - 1)` with respect to `c` is that of `u` with
respect to `b`: `u ↦ c.det (v, u)` is an alternating form on `W` taking the value `1` on `b`. -/
theorem det_finCons_eq_det (b : Basis (Fin k) R W) (c : Basis (Fin (k + 1)) R V)
    (hc : ⇑c = Fin.cons v (W.subtype ∘ b)) (u : Fin k → W) :
    c.det (Fin.cons v (W.subtype ∘ u)) = b.det u := by
  let f : W [⋀^Fin k]→ₗ[R] R := (c.det.curryLeft v).compLinearMap W.subtype
  have hf (u : Fin k → W) : f u = c.det (Fin.cons v (W.subtype ∘ u)) := by
    simp only [f, AlternatingMap.compLinearMap_apply, AlternatingMap.curryLeft_apply_apply,
      Matrix.vecCons, Function.comp_def]
  have h1 : f b = 1 := by rw [hf, ← hc, c.det_self]
  rw [← hf, f.eq_smul_basis_det b, h1, one_smul]

end CommRing

section DivisionRing

variable {K V : Type*} [DivisionRing K] [AddCommGroup V] [Module K V] {k : ℕ}
  {W : Submodule K V}

/-- **A vector outside a hyperplane, followed by a basis of the hyperplane, is a basis.** For a
space `V` of dimension `k + 1`, a basis `b` of a subspace `W` indexed by `Fin k` and `v ∉ W`, the
vectors `v, b 0, …, b (k - 1)` form a basis of `V`. -/
def mkFinConsOfNotMem (v : V) (b : Basis (Fin k) K W) (hv : v ∉ W) (hV : finrank K V = k + 1) :
    Basis (Fin (k + 1)) K V :=
  basisOfLinearIndependentOfCardEqFinrank
    ((b.linearIndependent.map' W.subtype W.ker_subtype).finCons (by
      rwa [Set.range_comp, Submodule.span_image, b.span_eq, Submodule.map_subtype_top]))
    (by rw [Fintype.card_fin, hV])

@[simp]
theorem coe_mkFinConsOfNotMem (v : V) (b : Basis (Fin k) K W) (hv : v ∉ W)
    (hV : finrank K V = k + 1) : ⇑(mkFinConsOfNotMem v b hv hV) = Fin.cons v (W.subtype ∘ b) :=
  coe_basisOfLinearIndependentOfCardEqFinrank _ _

end DivisionRing

section Field

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {k : ℕ} {W : Submodule K V}

/-- **The vectors `v, b 0, …, b (k - 1)` form a basis.** For a basis `b` of a subspace `W` of
codimension one and `v ∉ W`, their determinant with respect to any basis of `V` is nonzero. -/
theorem det_finCons_ne_zero (e : Basis (Fin (k + 1)) K V) (b : Basis (Fin k) K W) {v : V}
    (hv : v ∉ W) : e.det (Fin.cons v (W.subtype ∘ b)) ≠ 0 := by
  have hV : finrank K V = k + 1 := by rw [finrank_eq_card_basis e, Fintype.card_fin]
  rw [← coe_mkFinConsOfNotMem v b hv hV]
  exact (e.isUnit_det _).ne_zero

/-- A nonzero vector of a finite-dimensional space of dimension `k + 1` has nonzero zeroth
coordinate in some basis indexed by `Fin (k + 1)`. -/
theorem exists_repr_zero_ne_zero [FiniteDimensional K V] (hk : finrank K V = k + 1) {v : V}
    (hv : v ≠ 0) : ∃ b : Basis (Fin (k + 1)) K V, b.repr v 0 ≠ 0 := by
  let b₀ := Module.finBasisOfFinrankEq K V hk
  obtain ⟨i₀, hi₀⟩ : ∃ i, b₀.repr v i ≠ 0 := by
    by_contra! h
    exact hv (b₀.repr.injective (by ext i; simp [h i]))
  exact ⟨b₀.reindex (Equiv.swap i₀ 0), by simpa using hi₀⟩

end Field

section Ring

variable {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]

/-- If a linear functional `f` takes the value one on `v`, then `v` followed by any basis `b` of
the kernel of `f` is a basis: `M` is the direct sum of `R v` and the kernel of `f`. -/
theorem exists_basis_finCons_of_apply_eq_one {f : M →ₗ[R] R} {v : M} (hf : f v = 1) {m : ℕ}
    (b : Basis (Fin m) R (LinearMap.ker f)) :
    ∃ c : Basis (Fin (m + 1)) R M, c 0 = v ∧ ∀ i, c i.succ = b i := by
  refine ⟨.mkFinCons v b (fun a x hx hax ↦ ?_) (fun z ↦ ⟨-f z, by simp [hf]⟩), by simp, by simp⟩
  simpa [hf, LinearMap.mem_ker.1 hx] using congrArg f hax

end Ring

end Module.Basis
