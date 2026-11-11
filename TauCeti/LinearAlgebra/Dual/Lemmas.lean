/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Linear functionals and hyperplanes

A functional `f` with `f x = 1` splits a module into the line through `x` and the kernel of `f`.
This file records the projection `id - f(·) • x` that this splitting defines, and the dimension
count for the trace of `ker f` on a subspace on which `f` does not vanish. A basis `X` with
`f (X j) ≠ 0` yields a basis of `ker f` by moving each other `X i` into `ker f` along `X j`.
A codimension-one subspace, even in an infinite-dimensional ambient space, is the kernel
of a nonzero functional. Since functionals separate points, a vector space whose endomorphism
algebra is finite-dimensional is itself finite-dimensional.
Over a field, a linearly independent family of vectors has a biorthogonal family of functionals,
and on a finite-dimensional space a linearly independent family of functionals has a biorthogonal
family of vectors. Linearly independent functionals, as many as the dimension, span the dual space
and so separate points.

## Main results

* `Module.Dual.ker_id_sub_smulRight`: if `f x = 1`, the kernel of `id - f(·) • x` is the line
  through `x`.
* `Module.Dual.finrank_ker_inf_add_one`: if `f` does not vanish on a finite-dimensional subspace
  `U`, then `ker f ⊓ U` has codimension one in `U`. This is the relative form of Mathlib's
  `Module.Dual.finrank_ker_add_one_of_ne_zero`.
* `Module.Dual.finrank_quotient_ker_eq_one_of_ne_zero`: the kernel of a nonzero functional has
  codimension one.
* `Module.Dual.apply_smul_eq_apply_smul_of_finrank_eq_one`: any two functionals on a line are
  proportional, `c w • ψ = ψ w • c`.
* `Module.Dual.smul_evalEquiv_symm_dualMap`: on a line `L`, the vector whose pairings are
  `ψ ↦ β (C.symm ψ)` for `C : P ≃ L^*` is `β p / C p w` times `w`, in the multiplied-out form
  `C p w • x = β p • w`.
* `Module.Dual.linearIndependent_sub_div_smul` and `Module.Dual.span_sub_div_smul_eq_ker`: if
  `X` is a basis and `f (X j) ≠ 0`, the vectors `X i - (f (X i) / f (X j)) • X j`, `i ≠ j`, form a
  basis of `ker f`.
* `Submodule.exists_dual_ker_eq_of_finrank_quotient_eq_one`: every codimension-one subspace
  is the kernel of a nonzero functional.
* `Submodule.exists_dual_apply_eq_one_of_ne_top`: if a subspace `p` is not everything, some
  functional vanishes on `p` and equals one at some vector.
* `Module.Finite.of_finite_end`: a vector space is finite-dimensional once its endomorphism
  algebra is.
* `LinearIndependent.exists_dual_forall_apply_eq_ite`: a linearly independent family of vectors
  has a biorthogonal family of functionals, `f i (v j) = if i = j then 1 else 0`.
* `LinearIndependent.exists_forall_apply_eq_ite_of_dual`: on a finite-dimensional space, a linearly
  independent family of functionals has a biorthogonal family of vectors.
* `LinearIndependent.eq_zero_of_forall_apply_eq_zero`: linearly independent functionals, as many
  as the dimension, have no common zero but `0`.
* `LinearIndependent.exists_sum_smul_eq_proj`, `LinearIndependent.pi_bijective`,
  `LinearIndependent.det_pi_ne_zero`: `#ι` linearly independent forms on `Kⁱ` express every
  coordinate projection and assemble into a bijective endomorphism of nonzero determinant.
* `Matrix.of_apply_eq_mul_transpose_toMatrix'_pi` and `Matrix.det_of_apply_eq_det_mul_det_pi`:
  evaluating linear forms `l` on `ι → R` against vectors `x` multiplies `Matrix.of x` on the right
  by `(LinearMap.toMatrix' (LinearMap.pi l))ᵀ`, so for `#ι` forms and `#ι` vectors its determinant
  is `(Matrix.of x).det * LinearMap.det (LinearMap.pi l)`.
-/

public section

namespace Module.Dual

open Module

section Semiring

variable {K V : Type*} [Semiring K] [AddCommGroup V] [Module K V]

/-- If `f x = 1`, the kernel of `id - f(·) • x` is the line through `x`. -/
@[simp]
theorem ker_id_sub_smulRight (f : Dual K V) {x : V} (hfx : f x = 1) :
    LinearMap.ker (LinearMap.id - LinearMap.smulRight f x) = K ∙ x := by
  ext y
  simp only [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply,
    LinearMap.smulRight_apply, sub_eq_zero, Submodule.mem_span_singleton]
  exact ⟨fun h => ⟨f y, h.symm⟩, by rintro ⟨c, rfl⟩; simp [hfx]⟩

end Semiring

section DivisionRing

variable {K V : Type*} [DivisionRing K] [AddCommGroup V] [Module K V]

/-- If a functional `f` does not vanish on a finite-dimensional subspace `U`, then `ker f ⊓ U` has
codimension one in `U`. -/
theorem finrank_ker_inf_add_one {f : Dual K V} {U : Submodule K V} [FiniteDimensional K U]
    (hU : ¬ U ≤ LinearMap.ker f) :
    finrank K ↥(LinearMap.ker f ⊓ U) + 1 = finrank K U := by
  have hne : f.domRestrict U ≠ 0 := fun h => hU fun x hx => by
    simpa using LinearMap.congr_fun h ⟨x, hx⟩
  have hker : LinearMap.ker (f.domRestrict U) = (LinearMap.ker f ⊓ U).comap U.subtype := by
    rw [LinearMap.ker_domRestrict, Submodule.comap_inf, Submodule.comap_subtype_self, inf_top_eq]
  have hfin := finrank_ker_add_one_of_ne_zero hne
  rwa [hker, (Submodule.comapSubtypeEquivOfLe inf_le_right).finrank_eq] at hfin

/-- A hyperplane contained in the kernel of a nonzero functional equals that kernel. -/
theorem ker_eq_of_le_of_finrank_add_one (f : Dual K V)
    (hf : f ≠ 0) {S : Submodule K V} (hle : S ≤ LinearMap.ker f)
    (hdim : finrank K S + 1 = finrank K V) : LinearMap.ker f = S := by
  -- the hypothesis `hdim` forces `V` to be finite-dimensional
  have : FiniteDimensional K V := Module.finite_of_finrank_pos (by omega)
  apply (Submodule.eq_of_le_of_finrank_eq hle ?_).symm
  have hker := finrank_ker_add_one_of_ne_zero hf
  omega

/-- The kernel of a nonzero functional has codimension one. The ambient vector space need not be
finite-dimensional. -/
theorem finrank_quotient_ker_eq_one_of_ne_zero {f : Dual K V} (hf : f ≠ 0) :
    finrank K (V ⧸ LinearMap.ker f) = 1 := by
  rw [(f.quotKerEquivOfSurjective (LinearMap.surjective_iff_ne_zero.2 hf)).finrank_eq,
    finrank_self]

/-- Subtracting from each `X i`, `i ≠ j`, a multiple of `X j` preserves linear independence. The
multiples `f (X i) / f (X j)` are those that move `X i` into the kernel of `f`. -/
theorem linearIndependent_sub_div_smul (f : Dual K V) {ι : Type*} {X : ι → V}
    (hX : LinearIndependent K X) (j : ι) :
    LinearIndependent K fun i : {i // i ≠ j} ↦ X i - (f (X i) / f (X j)) • X j := by
  classical
  have h := (linearIndependent_add_smul_iff (v := X)
    (c := Function.update (fun i ↦ -(f (X i) / f (X j))) j 0) (Function.update_self _ _ _)).2 hX
  convert h.comp Subtype.val Subtype.val_injective using 1
  ext i
  simp [Function.update_of_ne i.2, sub_eq_add_neg]

/-- If `X` is a family of `finrank K V` linearly independent vectors and `f (X j) ≠ 0`, the vectors
`X i - (f (X i) / f (X j)) • X j`, `i ≠ j`, span the kernel of `f`. Together with
`Module.Dual.linearIndependent_sub_div_smul`, they form a basis of `ker f`. -/
theorem span_sub_div_smul_eq_ker (f : Dual K V) {ι : Type*} [Fintype ι]
    {X : ι → V} (hX : LinearIndependent K X) (hcard : Fintype.card ι = finrank K V) {j : ι}
    (hj : f (X j) ≠ 0) :
    Submodule.span K (Set.range fun i : {i // i ≠ j} ↦ X i - (f (X i) / f (X j)) • X j) =
      LinearMap.ker f := by
  classical
  -- the index `j` makes `ι` nonempty, so `hcard` forces `V` to be finite-dimensional
  have : FiniteDimensional K V :=
    Module.finite_of_finrank_pos (hcard ▸ Fintype.card_pos_iff.2 ⟨j⟩)
  have hli := f.linearIndependent_sub_div_smul hX j
  refine Submodule.eq_of_le_of_finrank_eq ?_ ?_
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    simp [hj]
  · have hker := finrank_ker_add_one_of_ne_zero fun h : f = 0 ↦ hj (by simp [h])
    rw [finrank_span_eq_card hli, Fintype.card_subtype_compl, Fintype.card_subtype_eq, hcard]
    exact Nat.sub_eq_of_eq_add hker.symm

end DivisionRing

section Field

variable {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- The rank of a family of forms restricted to a finite-dimensional subspace is the
codimension, in that subspace, of their common kernel. -/
theorem finrank_span_restrict_add_finrank_inf_iInf_ker (L : ι → Dual K V)
    (U : Submodule K V) [FiniteDimensional K U] (s : Set ι) :
    finrank K (Submodule.span K ((fun i ↦ (L i).comp U.subtype) '' s)) +
      finrank K ↥(U ⊓ ⨅ i ∈ s, LinearMap.ker (L i)) = finrank K U := by
  let A := Submodule.span K ((fun i ↦ (L i).comp U.subtype) '' s)
  have hA : A.dualCoannihilator =
      (U ⊓ ⨅ i ∈ s, LinearMap.ker (L i)).comap U.subtype := by
    dsimp only [A]
    rw [SetLike.ext'_iff, Submodule.coe_dualCoannihilator_span]
    ext x
    simp
  have h := Subspace.finrank_add_finrank_dualCoannihilator_eq A
  rw [hA, (Submodule.comapSubtypeEquivOfLe
    (inf_le_left : U ⊓ ⨅ i ∈ s, LinearMap.ker (L i) ≤ U)).finrank_eq] at h
  exact h

/-- Any two functionals on a line are proportional: `c w • ψ = ψ w • c` for every vector `w`. -/
theorem apply_smul_eq_apply_smul_of_finrank_eq_one (hV : finrank K V = 1) (c ψ : Dual K V)
    (w : V) : c w • ψ = ψ w • c := by
  obtain ⟨e, -, he⟩ := finrank_eq_one_iff'.mp hV
  ext z
  obtain ⟨s, rfl⟩ := he w
  obtain ⟨t, rfl⟩ := he z
  simp only [LinearMap.smul_apply, map_smul, smul_eq_mul]
  ring

/-- In a line `L`, let `x` be the vector with pairings `ψ x = β (C.symm ψ)`, for an isomorphism
`C : P ≃ L^*` and a functional `β` on `P`. Then `C p w • x = β p • w` for all `p` and `w`. -/
theorem smul_evalEquiv_symm_dualMap {L P : Type*} [AddCommGroup L] [Module K L]
    [FiniteDimensional K L] [AddCommGroup P] [Module K P] (hL : finrank K L = 1)
    (C : P ≃ₗ[K] Dual K L) (β : Dual K P) (p : P) (w : L) :
    C p w • (evalEquiv K L).symm (C.symm.dualMap β) = β p • w := by
  rw [← sub_eq_zero]
  refine (forall_dual_apply_eq_zero_iff K _).mp fun ψ ↦ ?_
  -- Applying `β ∘ C.symm` to the proportionality `C p w • ψ = ψ w • C p` of functionals on `L`.
  have h := congrArg (fun q ↦ β (C.symm q))
    ((C p).apply_smul_eq_apply_smul_of_finrank_eq_one hL ψ w)
  simp only [map_smul, LinearEquiv.symm_apply_apply, smul_eq_mul] at h
  simp only [map_sub, map_smul, apply_evalEquiv_symm_apply, LinearEquiv.dualMap_apply, smul_eq_mul,
    h, mul_comm, sub_self]

end Field

end Module.Dual

namespace Submodule

variable {K V : Type*} [DivisionRing K] [AddCommGroup V] [Module K V]

/-- A subspace of codimension one is the kernel of a nonzero linear functional.
The ambient vector space need not be finite-dimensional. -/
theorem exists_dual_ker_eq_of_finrank_quotient_eq_one (W : Submodule K V)
    (hW : Module.finrank K (V ⧸ W) = 1) :
    ∃ ℓ : Module.Dual K V, ℓ ≠ 0 ∧ LinearMap.ker ℓ = W := by
  have : FiniteDimensional K (V ⧸ W) := Module.finite_of_finrank_pos (by omega)
  let e := LinearEquiv.ofFinrankEq (R := K) (V ⧸ W) K (by simpa using hW)
  refine ⟨e.toLinearMap.comp W.mkQ, ?_, ?_⟩
  · intro h
    have he : Function.Surjective (e.toLinearMap.comp W.mkQ) :=
      e.surjective.comp W.mkQ_surjective
    obtain ⟨v, hv⟩ := he 1
    simp [h] at hv
  · ext v
    simp

/-- If a subspace `p` is not the whole space, some linear functional vanishes on `p` and takes the
value `1` at some vector. -/
theorem exists_dual_apply_eq_one_of_ne_top {p : Submodule K V} (hp : p ≠ ⊤) :
    ∃ (f : Module.Dual K V) (z : V), f z = 1 ∧ p ≤ LinearMap.ker f := by
  obtain ⟨z, hz⟩ := SetLike.exists_notMem_of_ne_top p hp rfl
  obtain ⟨f, hfz, hfp⟩ := exists_dual_map_eq_bot_of_notMem hz inferInstance
  refine ⟨f, (f z)⁻¹ • z, by simp [hfz], fun x hx ↦ ?_⟩
  have hxmap : f x ∈ p.map f := ⟨x, hx, rfl⟩
  rw [hfp, mem_bot] at hxmap
  exact hxmap

end Submodule

namespace Module.Finite

/-- A vector space whose endomorphism algebra is finite-dimensional is finite-dimensional: for
`x ≠ 0`, evaluation at `x` maps `End_K S` onto `S`. -/
theorem of_finite_end (K S : Type*) [Field K] [AddCommGroup S] [Module K S]
    [Module.Finite K (Module.End K S)] : Module.Finite K S := by
  rcases subsingleton_or_nontrivial S with _ | _
  · infer_instance
  obtain ⟨x, hx⟩ := exists_ne (0 : S)
  obtain ⟨φ, hφ⟩ : ∃ φ : Dual K S, φ x ≠ 0 := by
    by_contra! h
    exact hx ((forall_dual_apply_eq_zero_iff K x).1 h)
  exact Module.Finite.of_surjective (LinearMap.applyₗ x)
    fun y ↦ ⟨(φ x)⁻¹ • φ.smulRight y, by simp [hφ]⟩

end Module.Finite

namespace LinearIndependent

open Module

section Biorthogonal

variable {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V] [DecidableEq ι]

/-- A linearly independent family of vectors has a **biorthogonal family of functionals**:
`f i (v j)` is `1` for `i = j` and `0` otherwise. The functional `f i` extends the `i`-th
coordinate on the span of the family. -/
theorem exists_dual_forall_apply_eq_ite {v : ι → V} (hv : LinearIndependent K v) :
    ∃ f : ι → Dual K V, ∀ i j, f i (v j) = if i = j then 1 else 0 := by
  choose f hf using fun i ↦ LinearMap.exists_extend ((Finsupp.lapply i).comp hv.repr)
  refine ⟨f, fun i j ↦ ?_⟩
  have hj : v j ∈ Submodule.span K (Set.range v) := Submodule.subset_span ⟨j, rfl⟩
  have := LinearMap.congr_fun (hf i) ⟨v j, hj⟩
  rw [LinearMap.comp_apply, Submodule.subtype_apply] at this
  rw [this, LinearMap.comp_apply, hv.repr_eq_single j _ rfl,
    Finsupp.lapply_apply, Finsupp.single_apply]
  exact if_congr eq_comm rfl rfl

/-- On a finite-dimensional space, a linearly independent family of functionals has a
**biorthogonal family of vectors**: `f i (v j)` is `1` for `i = j` and `0` otherwise. -/
theorem exists_forall_apply_eq_ite_of_dual [FiniteDimensional K V] {f : ι → Dual K V}
    (hf : LinearIndependent K f) :
    ∃ v : ι → V, ∀ i j, f i (v j) = if i = j then 1 else 0 := by
  obtain ⟨g, hg⟩ := hf.exists_dual_forall_apply_eq_ite
  refine ⟨fun j ↦ (evalEquiv K V).symm (g j), fun i j ↦ ?_⟩
  rw [apply_evalEquiv_symm_apply, hg]
  exact if_congr eq_comm rfl rfl

end Biorthogonal

section Separation

variable {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  [Fintype ι]

/-- Linearly independent linear forms, as many as the dimension, have no common zero but `0`. -/
theorem eq_zero_of_forall_apply_eq_zero {L : ι → Module.Dual K V} (hL : LinearIndependent K L)
    (hcard : Fintype.card ι = Module.finrank K V) {z : V} (hz : ∀ i, L i z = 0) : z = 0 := by
  have hspan := hL.span_eq_top_of_card_eq_finrank' <| by rwa [Subspace.dual_finrank_eq]
  have hz' : z ∈ (Submodule.span K (Set.range L)).dualCoannihilator := by
    rw [← SetLike.mem_coe, Submodule.coe_dualCoannihilator_span]
    rintro _ ⟨i, rfl⟩
    exact hz i
  rw [hspan] at hz'
  simpa using hz'

end Separation

/-- `#ι` linearly independent forms on `Kⁱ` span its dual, so every coordinate projection is a
combination of them. -/
theorem exists_sum_smul_eq_proj {K ι : Type*} [Field K] [Fintype ι]
    {l : ι → Module.Dual K (ι → K)} (hl : LinearIndependent K l) :
    ∃ a : ι → ι → K, ∀ j, ∑ i, a j i • l i = LinearMap.proj j := by
  have hspan : Submodule.span K (Set.range l) = ⊤ :=
    hl.span_eq_top_of_card_eq_finrank' (by simp [Subspace.dual_finrank_eq])
  choose a ha using fun j : ι ↦ (Submodule.mem_span_range_iff_exists_fun K).mp
    (hspan ▸ Submodule.mem_top : LinearMap.proj (φ := fun _ : ι ↦ K) j ∈ _)
  exact ⟨a, ha⟩

/-- `#ι` linearly independent forms on `Kⁱ` assemble into a bijective endomorphism
`LinearMap.pi l`. -/
theorem pi_bijective {K ι : Type*} [Field K] [Finite ι]
    {l : ι → Module.Dual K (ι → K)} (hl : LinearIndependent K l) :
    Function.Bijective (LinearMap.pi l) := by
  have := Fintype.ofFinite ι
  have hinj : Function.Injective (LinearMap.pi l) :=
    LinearMap.ker_eq_bot.mp <| eq_bot_iff.mpr fun x hx ↦
      hl.eq_zero_of_forall_apply_eq_zero (by simp) fun i ↦ congr_fun hx i
  exact ⟨hinj, LinearMap.injective_iff_surjective.mp hinj⟩

/-- `#ι` linearly independent forms on `Kⁱ` have nonzero determinant
`LinearMap.det (LinearMap.pi l)`. -/
theorem det_pi_ne_zero {K ι : Type*} [Field K] [Finite ι]
    {l : ι → Module.Dual K (ι → K)} (hl : LinearIndependent K l) :
    LinearMap.det (LinearMap.pi l) ≠ 0 :=
  (LinearMap.isUnit_iff_isUnit_det (LinearMap.pi l) |>.mp
    (Module.End.isUnit_iff (LinearMap.pi l) |>.mpr hl.pi_bijective)).ne_zero

end LinearIndependent

namespace Matrix

/-- Evaluating a family of linear forms `l` on `ι → R` against a family of vectors `x` multiplies
`Matrix.of x` on the right by `(LinearMap.toMatrix' (LinearMap.pi l))ᵀ`. -/
theorem of_apply_eq_mul_transpose_toMatrix'_pi {R κ ι μ : Type*} [CommSemiring R] [Fintype ι]
    [DecidableEq ι] (l : μ → Module.Dual R (ι → R)) (x : κ → ι → R) :
    Matrix.of (fun k i ↦ l i (x k)) = Matrix.of x * (LinearMap.toMatrix' (LinearMap.pi l))ᵀ := by
  ext k i
  conv_lhs => rw [of_apply, ← (Pi.basisFun R ι).sum_repr (x k), map_sum]
  simp [Matrix.mul_apply, LinearMap.toMatrix'_apply]

/-- The determinant of `(l i (x k))_{k, i}` for `#ι` linear forms `l` and `#ι` vectors `x` on
`ι → R` equals `(Matrix.of x).det * LinearMap.det (LinearMap.pi l)`. -/
theorem det_of_apply_eq_det_mul_det_pi {R ι : Type*} [CommRing R] [Fintype ι] [DecidableEq ι]
    (l : ι → Module.Dual R (ι → R)) (x : ι → ι → R) :
    (Matrix.of fun k i ↦ l i (x k)).det = (Matrix.of x).det * LinearMap.det (LinearMap.pi l) := by
  rw [of_apply_eq_mul_transpose_toMatrix'_pi, det_mul, det_transpose, LinearMap.det_toMatrix']

end Matrix
