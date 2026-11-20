/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.Dual.Lemmas

import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import TauCeti.LinearAlgebra.LinearIndependent.Extend

/-!
# Linear functionals and hyperplanes

A functional `f` with `f x = 1` splits a module into the line through `x` and the kernel of `f`.
This file records the projection `id - f(·) • x` that this splitting defines, the factorization
of `r • id` through `f` when `r` annihilates `ker f`, and the dimension count for the trace of
`ker f` on a subspace on which `f` does not vanish. A basis `X` with `f (X j) ≠ 0` yields a basis
of `ker f` by moving each other `X i` into `ker f` along `X j`.
A codimension-one subspace, even in an infinite-dimensional ambient space, is the kernel
of a nonzero functional. Since functionals separate points, a vector space whose endomorphism
algebra is finite-dimensional is itself finite-dimensional.
Over a field, a linearly independent family of vectors has a biorthogonal family of functionals,
and on a finite-dimensional space a linearly independent family of functionals has a biorthogonal
family of vectors. Linearly independent functionals, as many as the dimension, span the dual space
and so separate points. Conversely, a separating family of functionals on a finite-dimensional
space contains such a family, which gives coordinates on the space.

## Main results

* `Module.Dual.ker_id_sub_smulRight`: if `f x = 1`, the kernel of `id - f(·) • x` is the line
  through `x`.
* `Module.Dual.smulRight_smul_eq_smul_id`: if `f x = 1` and `r` annihilates `ker f`, then
  `r • id` factors through `f` as `y ↦ (r • f) y • x`.
* `Module.Dual.eval_eq_applyₗ`: evaluation into the double dual is `LinearMap.applyₗ`.
* `Module.Dual.linearIndependent_iff_apply_basis`: a family of forms is linearly independent
  exactly when the family of its coefficient vectors with respect to a basis is.
* `Module.Dual.linearIndependent_proj` and `Module.Dual.span_range_proj_eq_top`: the coordinate
  projections on `ι → R` are linearly independent in the dual space, and span it when `ι` is
  finite.
* `Module.Dual.apply_eq_mul_apply_of_nonneg`: over an ordered ring, if `f x = 1`, a functional `g`
  nonnegative on the half-space `{v | 0 ≤ f v}` is the multiple `g x • f` of `f`.
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
* `Module.Dual.span_range_comp_eq_top_of_injective`: pulling a spanning family of forms back along
  an injective linear map still spans the dual.
* `Submodule.exists_dual_ker_eq_of_finrank_quotient_eq_one`: every codimension-one subspace
  is the kernel of a nonzero functional.
* `Submodule.exists_dual_apply_eq_one_of_ne_top`: if a subspace `p` is not everything, some
  functional vanishes on `p` and equals one at some vector.
* `Module.Finite.of_finite_end`: a vector space is finite-dimensional once its endomorphism
  algebra is, and `Module.Finite.of_surjective_end`: in particular once a finite-dimensional space
  maps linearly onto its endomorphism algebra.
* `LinearMap.finrank_range_flip`: a pairing `B : V₁ →ₗ[K] V₂ →ₗ[K] K` with `V₂` reflexive and
  its transpose `B.flip` have the same rank.
* `LinearIndependent.exists_dual_forall_apply_eq_ite`: a linearly independent family of vectors
  has a biorthogonal family of functionals, `f i (v j) = if i = j then 1 else 0`.
* `LinearIndependent.exists_forall_apply_eq_ite_of_dual`: on a finite-dimensional space, a linearly
  independent family of functionals has a biorthogonal family of vectors.
* `LinearIndependent.eq_zero_of_forall_apply_eq_zero`: linearly independent functionals, as many
  as the dimension, have no common zero but `0`.
* `LinearIndependent.exists_sum_smul_eq_proj`, `LinearIndependent.pi_bijective`,
  `LinearIndependent.det_pi_ne_zero`: `#ι` linearly independent forms on `Kⁱ` express every
  coordinate projection and assemble into a bijective endomorphism of nonzero determinant.
* `Module.Dual.span_range_proj` and `LinearIndependent.exists_linearIndependent_sumElim_proj`: the
  coordinate forms span the dual of `Rⁱ`, so over a field a linearly independent family of forms
  extends by coordinate forms to a basis of the dual.
* `Module.Dual.exists_bijective_pi_of_iInf_ker_eq_bot`: on a finite-dimensional space, a family
  of functionals with no common zero but `0` contains `finrank K V` members that form coordinates.
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

section CommRing

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

/-- If `f x = 1` and `r` annihilates the kernel of `f`, then multiplication by `r` factors through
`f`: `r • y = (r • f) y • x`, since `y - f y • x` lies in the kernel of `f`. -/
theorem smulRight_smul_eq_smul_id (f : Dual R V) {x : V} (hfx : f x = 1) {r : R}
    (hr : ∀ y ∈ LinearMap.ker f, r • y = 0) :
    LinearMap.smulRight (r • f) x = r • LinearMap.id := by
  ext y
  have h := hr (y - f y • x) (by simp [hfx])
  rw [smul_sub, sub_eq_zero] at h
  simp [h, smul_smul]

end CommRing

section CommSemiring

section Basis

variable {R M ι κ : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]

/-- A family of forms is linearly independent exactly when the family of their coefficient
vectors, the values on a basis, is. -/
theorem linearIndependent_iff_apply_basis (b : Basis ι R M) {L : κ → Dual R M} :
    LinearIndependent R L ↔ LinearIndependent R (fun i j ↦ L i (b j)) := by
  let e : Dual R M ≃ₗ[R] (ι → R) := (b.constr R).symm
  have he : (fun i j ↦ L i (b j)) = e ∘ L := by
    ext
    simp [e]
  rw [he]
  exact (e.toLinearMap.linearIndependent_iff_of_injOn e.injective.injOn).symm

end Basis

section Proj

variable (R ι : Type*) [CommSemiring R]

/-- Evaluation into the double dual is evaluation into the double `R`-valued `Hom`. -/
theorem eval_eq_applyₗ (M : Type*) [AddCommMonoid M] [Module R M] :
    Dual.eval R M = LinearMap.applyₗ :=
  LinearMap.ext fun _ ↦ LinearMap.ext fun _ ↦ by simp

/-- The coordinate projections on `ι → R` are linearly independent in the dual space. -/
theorem linearIndependent_proj :
    LinearIndependent R (fun i : ι ↦ (LinearMap.proj i : Dual R (ι → R))) := by
  classical
  refine linearIndependent_iff'ₛ.mpr fun s l₁ l₂ h j hj ↦ ?_
  simpa [hj, Pi.single_apply] using LinearMap.congr_fun h (Pi.single j (1 : R))

/-- The coordinate projections on `ι → R` span the dual space when `ι` is finite. -/
theorem span_range_proj_eq_top [Finite ι] :
    Submodule.span R (Set.range fun i : ι ↦ (LinearMap.proj i : Dual R (ι → R))) = ⊤ := by
  classical
  have h : ⇑(Pi.basisFun R ι).dualBasis = fun i ↦ (LinearMap.proj i : Dual R (ι → R)) := by
    ext i x
    simp
  exact h ▸ (Pi.basisFun R ι).dualBasis.span_eq

end Proj

end CommSemiring

section OrderedCommRing

variable {R V : Type*} [CommRing R] [PartialOrder R] [IsOrderedAddMonoid R] [AddCommGroup V]
  [Module R V]

/-- If `f x = 1`, a functional `g` that is nonnegative on the half-space `{v | 0 ≤ f v}` is the
multiple `g x • f` of `f`. -/
theorem apply_eq_mul_apply_of_nonneg (f g : Dual R V) {x : V} (hfx : f x = 1)
    (hg : ∀ v, 0 ≤ f v → 0 ≤ g v) (u : V) : g u = g x * f u := by
  -- `g` vanishes on the kernel of `f`, which contains `u - f u • x`.
  have hker (v : V) (hv : f v = 0) : g v = 0 :=
    le_antisymm (by simpa using hg (-v) (by simp [hv])) (hg v hv.ge)
  have hrest : f (u - f u • x) = 0 := by simp [hfx]
  calc
    g u = g (f u • x + (u - f u • x)) := by rw [add_sub_cancel]
    _ = g x * f u := by rw [map_add, hker _ hrest, map_smul, smul_eq_mul, add_zero, mul_comm]

end OrderedCommRing

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
  simp [Function.update_of_ne i.property, sub_eq_add_neg]

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

/-- Pulling a spanning family of forms back along an injective linear map still spans the dual. -/
theorem span_range_comp_eq_top_of_injective {W : Type*} [AddCommGroup W] [Module K W]
    {L : ι → Dual K V} (hL : Submodule.span K (Set.range L) = ⊤) {f : W →ₗ[K] V}
    (hf : Function.Injective f) :
    Submodule.span K (Set.range fun i ↦ (L i).comp f) = ⊤ := by
  simp_rw [← LinearMap.dualMap_apply', Set.range_comp', ← Submodule.map_span, hL,
    Submodule.map_top, LinearMap.range_eq_top]
  exact LinearMap.dualMap_surjective_of_injective hf

end Field

/-- The coordinate forms span the dual of `R^ι`. -/
theorem span_range_proj {R ι : Type*} [CommSemiring R] [Finite ι] :
    Submodule.span R (Set.range fun j : ι ↦ (LinearMap.proj j : Dual R (ι → R))) = ⊤ := by
  classical
  have := Fintype.ofFinite ι
  have h : (fun j : ι ↦ (LinearMap.proj j : Dual R (ι → R))) = (Pi.basisFun R ι).dualBasis := by
    ext j x
    simp
  rw [h, Basis.span_eq]

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

/-- A vector space is finite-dimensional if a finite-dimensional space maps linearly onto its
endomorphism algebra; for instance, a module over a finite-dimensional algebra `A` on which
`Algebra.lsmul : A → End_K S` is surjective. -/
theorem of_surjective_end {K E S F : Type*} [Field K] [AddCommMonoid E] [Module K E]
    [Module.Finite K E] [AddCommGroup S] [Module K S] [FunLike F E (Module.End K S)]
    [LinearMapClass F K E (Module.End K S)] (f : F) (hf : Function.Surjective f) :
    Module.Finite K S :=
  have : Module.Finite K (Module.End K S) := .of_surjective (f : E →ₗ[K] Module.End K S) hf
  .of_finite_end K S

end Module.Finite

namespace LinearMap

variable {K V₁ V₂ : Type*} [Field K] [AddCommGroup V₁] [Module K V₁] [AddCommGroup V₂]
  [Module K V₂] [Module.IsReflexive K V₂]

/-- **A pairing and its transpose have the same rank**: for `B : V₁ →ₗ[K] V₂ →ₗ[K] K` with `V₂`
reflexive, the transposed pairing `B.flip : V₂ →ₗ[K] Module.Dual K V₁` is `B.dualMap` composed
with the evaluation isomorphism of `V₂`, so its rank is that of `B`
(`LinearMap.finrank_range_dualMap_eq_finrank_range`). -/
theorem finrank_range_flip (B : V₁ →ₗ[K] V₂ →ₗ[K] K) :
    Module.finrank K (range B.flip) = Module.finrank K (range B) := by
  -- `B.flip` is definitionally `B.dualMap ∘ₗ evalEquiv`, as in Mathlib's
  -- `LinearMap.dualAnnihilator_ker_eq_range_flip`
  change Module.finrank K (range (B.dualMap ∘ₗ (Module.evalEquiv K V₂).toLinearMap)) = _
  rw [range_comp_of_range_eq_top _ (LinearEquiv.range _), finrank_range_dualMap_eq_finrank_range]

end LinearMap

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

open Finset in
/-- A linearly independent family `f` of forms on `Kⁱ` extends by coordinate forms to a basis of
the dual: for some finset `u` of coordinates, `Sum.elim f (proj ∘ (↑) : u → _)` is linearly
independent and has `card ι` members. -/
theorem exists_linearIndependent_sumElim_proj {K ι τ : Type*} [Field K] [Fintype ι] [Fintype τ]
    {f : τ → Module.Dual K (ι → K)} (hf : LinearIndependent K f) :
    ∃ u : Finset ι, LinearIndependent K
        (Sum.elim f fun j : u ↦ (LinearMap.proj (j : ι) : Module.Dual K (ι → K))) ∧
      Fintype.card τ + #u = Fintype.card ι := by
  classical
  obtain ⟨u, hli, hspan⟩ := hf.exists_linearIndependent_sumElim Module.Dual.span_range_proj
  refine ⟨u.toFinset, ?_, ?_⟩
  · convert hli.comp (Sum.map id (Equiv.subtypeEquivRight fun j ↦ Set.mem_toFinset))
      (Sum.map_injective.mpr ⟨Function.injective_id, Equiv.injective _⟩) using 1
    ext (k | j) <;> rfl
  · have hcard := Module.finrank_eq_card_basis (Basis.mk hli hspan.ge)
    rw [Subspace.dual_finrank_eq, Module.finrank_fintype_fun_eq_card, Fintype.card_sum] at hcard
    rw [hcard, Set.toFinset_card]

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

namespace Module.Dual

variable {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- **Coordinates from separating functionals.** On a finite-dimensional space, a family of
functionals with no common zero but `0` contains `finrank K V` members that assemble into a
linear isomorphism `V ≃ K^(finrank K V)`. -/
theorem exists_bijective_pi_of_iInf_ker_eq_bot [FiniteDimensional K V] (L : ι → Dual K V)
    (h : ⨅ i, LinearMap.ker (L i) = ⊥) :
    ∃ c : Fin (finrank K V) → ι, Function.Bijective (LinearMap.pi (L ∘ c)) := by
  have hspan : Submodule.span K (Set.range L) = ⊤ := Submodule.eq_top_iff'.mpr fun f ↦
    FiniteDimensional.mem_span_of_iInf_ker_le_ker (by simp [h])
  obtain ⟨κ, a, -, hspan', hli⟩ := exists_linearIndependent' K L
  rw [hspan] at hspan'
  let e : κ ≃ Fin (finrank K V) := (Basis.mk hli hspan'.ge).indexEquiv (finBasis K V).dualBasis
  refine ⟨a ∘ e.symm, ?_⟩
  have hinj : Function.Injective (LinearMap.pi (L ∘ a ∘ e.symm)) :=
    (injective_iff_map_eq_zero _).mpr fun x hx ↦
      (hli.comp _ e.symm.injective).eq_zero_of_forall_apply_eq_zero (by simp) fun i ↦
        congrFun hx i
  exact ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by simp)).mp hinj⟩

end Module.Dual

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
