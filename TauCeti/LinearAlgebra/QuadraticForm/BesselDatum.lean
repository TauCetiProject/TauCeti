/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.QuadraticForm.BaseChange
public import TauCeti.LinearAlgebra.QuadraticForm.Witt.TotallyIsotropic
import TauCeti.LinearAlgebra.BilinearForm.Orthogonal
import TauCeti.LinearAlgebra.Dual.Lemmas
import TauCeti.LinearAlgebra.QuadraticForm.Basic

/-!
# Orthogonal Bessel data

Let `Q` be a quadratic form on `V` over a ring in which `2` is invertible, and write
`B = QuadraticMap.associated Q` for the symmetric bilinear form with `B v v = Q v` (so that
`polar Q = 2 B`). An *orthogonal Bessel datum of index `ℓ`* consists of

* vectors `e₁, …, e_ℓ` spanning the isotropic flag `⟨e₁⟩ ⊂ ⟨e₁, e₂⟩ ⊂ ⋯ ⊂ ⟨e₁, …, e_ℓ⟩`,
* dual isotropic vectors `e₋₁, …, e₋ℓ`, with `B eᵢ eⱼ = B e₋ᵢ e₋ⱼ = 0` and `B eᵢ e₋ⱼ = δᵢⱼ`,
* an anisotropic vector `w` of the middle space `V_ℓ = ⟨e₋ℓ, …, e₋₁, e₁, …, e_ℓ⟩^⊥`.

These are the data from which Bessel coefficients of automorphic forms on `SO(V)` are built: the
unipotent radical of the stabilizer of the flag carries a character read off from the adjacent
flag coordinates and the pairing with `w`, and the Bessel subgroup is the special orthogonal group
of the orthogonal complement of `w` in `V_ℓ`. The normalization `B eᵢ e₋ⱼ = δᵢⱼ` is that of
the Gram matrix of Jiang–Zhang.

## Main definitions

* `TauCeti.OrthogonalBesselDatum Q ℓ`: an orthogonal Bessel datum of index `ℓ` for `Q`.
* `TauCeti.OrthogonalBesselDatum.flag`: the isotropic flag `⟨e₁, …, e_j⟩`.
* `TauCeti.OrthogonalBesselDatum.middleSpace`: the middle space `V_ℓ`.
* `TauCeti.OrthogonalBesselDatum.map`: transport along an isometry.
* `TauCeti.OrthogonalBesselDatum.baseChange`: extension of scalars.

## Main results

* `TauCeti.OrthogonalBesselDatum.linearIndependent`: the vectors `eᵢ`, `e₋ᵢ` and `w` are linearly
  independent.
* `TauCeti.OrthogonalBesselDatum.isCompl_span_middleSpace`: `V` is the direct sum of the span of
  the `e±ᵢ` and the middle space `V_ℓ`.
* `TauCeti.OrthogonalBesselDatum.nondegenerate_restrict_middleSpace`: in a regular quadratic
  space, the middle space `V_ℓ` is regular.
* `TauCeti.OrthogonalBesselDatum.finrank_flag`, `TauCeti.OrthogonalBesselDatum.finrank_middleSpace`:
  the flag subspaces have the expected dimensions, and `V_ℓ` has codimension `2ℓ`.
* `TauCeti.OrthogonalBesselDatum.nonempty_iff`: over a field of characteristic not two, a regular
  quadratic space of dimension `d` and Witt index `r` carries a Bessel datum of index `ℓ` exactly
  when `ℓ ≤ r` and `2ℓ + 1 ≤ d`.

## References

* D. Jiang, L. Zhang, *Arthur parameters and cuspidal automorphic modules of classical groups*,
  Ann. of Math. 191 (2020), §2.1 (the basis (2.1) and Gram matrix (2.2)) and §2.4.
-/

public section

open Module QuadraticMap

open scoped TensorProduct

namespace TauCeti

universe u v w

/-- An *orthogonal Bessel datum of index `ℓ`* for a quadratic form `Q`. Writing
`B = QuadraticMap.associated Q`, it consists of vectors `e₁, …, e_ℓ` (the field `e`) and
`e₋₁, …, e₋ℓ` (the field `f`) with `B eᵢ eₖ = B e₋ᵢ e₋ₖ = 0` and `B eᵢ e₋ₖ = δᵢₖ`, and a vector
`w` orthogonal to all of them with `Q w ≠ 0`. The isotropic flag of the datum is
`⟨e₁⟩ ⊂ ⋯ ⊂ ⟨e₁, …, e_ℓ⟩`, and `w` is an anisotropic vector of its middle space. -/
@[ext]
structure OrthogonalBesselDatum {R : Type u} {M : Type v} [CommRing R] [Invertible (2 : R)]
    [AddCommGroup M] [Module R M] (Q : QuadraticForm R M) (ℓ : ℕ) where
  /-- The vectors `e₁, …, e_ℓ` spanning the isotropic flag. -/
  e : Fin ℓ → M
  /-- The dual isotropic vectors `e₋₁, …, e₋ℓ`. -/
  f : Fin ℓ → M
  /-- The anisotropic vector of the middle space. -/
  w : M
  associated_e_e : ∀ i k, associated Q (e i) (e k) = 0
  associated_f_f : ∀ i k, associated Q (f i) (f k) = 0
  associated_e_f : ∀ i k, associated Q (e i) (f k) = if i = k then 1 else 0
  associated_e_w : ∀ i, associated Q (e i) w = 0
  associated_f_w : ∀ i, associated Q (f i) w = 0
  apply_w_ne_zero : Q w ≠ 0

namespace OrthogonalBesselDatum

section CommRing

variable {R : Type u} {M : Type v} {N : Type w} [CommRing R] [Invertible (2 : R)]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {Q : QuadraticForm R M} {ℓ : ℕ} (D : OrthogonalBesselDatum Q ℓ)

attribute [simp] associated_e_e associated_f_f associated_e_f associated_e_w associated_f_w

@[simp]
theorem associated_f_e (i k : Fin ℓ) :
    associated Q (D.f i) (D.e k) = if i = k then 1 else 0 := by
  rw [associated_isSymm, D.associated_e_f]
  exact if_congr eq_comm rfl rfl

@[simp]
theorem associated_w_e (i : Fin ℓ) : associated Q D.w (D.e i) = 0 := by
  rw [associated_isSymm, D.associated_e_w]

@[simp]
theorem associated_w_f (i : Fin ℓ) : associated Q D.w (D.f i) = 0 := by
  rw [associated_isSymm, D.associated_f_w]

@[simp]
theorem apply_e (i : Fin ℓ) : Q (D.e i) = 0 := by
  rw [← associated_eq_self_apply R, D.associated_e_e]

@[simp]
theorem apply_f (i : Fin ℓ) : Q (D.f i) = 0 := by
  rw [← associated_eq_self_apply R, D.associated_f_f]

theorem w_ne_zero : D.w ≠ 0 := fun h ↦ D.apply_w_ne_zero (by rw [h, map_zero])

/-! ### The flag and the middle space -/

/-- The `j`-th subspace `⟨e₁, …, e_j⟩` of the isotropic flag of a Bessel datum (the whole span
of the `eᵢ` once `j ≥ ℓ`). -/
def flag (j : ℕ) : Submodule R M :=
  Submodule.span R (D.e '' {i | (i : ℕ) < j})

theorem flag_mono : Monotone D.flag := fun _ _ hjk ↦
  Submodule.span_mono (Set.image_mono fun _ hi ↦ lt_of_lt_of_le hi hjk)

theorem e_mem_flag {i : Fin ℓ} {j : ℕ} (hij : (i : ℕ) < j) : D.e i ∈ D.flag j :=
  Submodule.subset_span ⟨i, hij, rfl⟩

@[simp]
theorem flag_zero : D.flag 0 = ⊥ := by simp [flag]

/-- From index `ℓ` on, the flag is the whole span of the `eᵢ`. -/
theorem flag_of_le {j : ℕ} (hj : ℓ ≤ j) : D.flag j = Submodule.span R (Set.range D.e) := by
  have h : {i : Fin ℓ | (i : ℕ) < j} = Set.univ :=
    Set.eq_univ_of_forall fun i ↦ i.isLt.trans_le hj
  rw [flag, h, Set.image_univ]

/-- Each step of the flag adjoins one vector: `⟨e₁, …, e_{i+1}⟩ = ⟨e₁, …, e_i⟩ ⊔ ⟨e_{i+1}⟩`. -/
@[simp]
theorem flag_succ (i : Fin ℓ) : D.flag (i + 1) = D.flag i ⊔ R ∙ D.e i := by
  have h : {k : Fin ℓ | (k : ℕ) < i + 1} = insert i {k : Fin ℓ | (k : ℕ) < i} := by
    ext k
    simp [le_iff_eq_or_lt, Fin.val_inj]
  rw [flag, flag, h, Set.image_insert_eq, Submodule.span_insert, sup_comm]

/-- Every subspace of the flag is totally isotropic. -/
theorem isTotallyIsotropic_flag (j : ℕ) : Q.IsTotallyIsotropic (D.flag j) := by
  -- Every vector of the flag is `associated Q`-orthogonal to every vector of the flag.
  have hle : D.flag j ≤ LinearMap.BilinForm.orthogonal (associated Q) (D.flag j) := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨i, -, rfl⟩
    rw [SetLike.mem_coe, flag, LinearMap.BilinForm.orthogonal, Submodule.mem_orthogonalBilin_span]
    rintro _ ⟨k, -, rfl⟩
    exact D.associated_e_e k i
  rw [isTotallyIsotropic_iff]
  intro x hx
  rw [← associated_eq_self_apply R]
  exact (LinearMap.BilinForm.mem_orthogonal_iff.mp (hle hx)) x hx

/-- The middle space `V_ℓ` of a Bessel datum: the orthogonal complement of the span of the
vectors `e₋ℓ, …, e₋₁, e₁, …, e_ℓ`. -/
def middleSpace : Submodule R M :=
  LinearMap.BilinForm.orthogonal (associated Q) (Submodule.span R (Set.range D.e ∪ Set.range D.f))

@[simp]
theorem mem_middleSpace_iff {x : M} :
    x ∈ D.middleSpace ↔ (∀ i, associated Q (D.e i) x = 0) ∧ ∀ i, associated Q (D.f i) x = 0 := by
  simp only [middleSpace, LinearMap.BilinForm.orthogonal, Submodule.mem_orthogonalBilin_span,
    Set.forall_mem_union, Set.forall_mem_range]

theorem w_mem_middleSpace : D.w ∈ D.middleSpace :=
  D.mem_middleSpace_iff.mpr ⟨D.associated_e_w, D.associated_f_w⟩

/-- The coordinates `v ↦ (B e₋ₖ v, B eₖ v)` dual to the vectors `eₖ` and `e₋ₖ`. -/
private def coords : M →ₗ[R] Fin ℓ ⊕ Fin ℓ → R :=
  LinearMap.pi (Sum.elim (fun k ↦ associated Q (D.f k)) fun k ↦ associated Q (D.e k))

/-- Pairing with `e₋ₖ` and `eₖ` sends the vectors `eᵢ`, `e₋ᵢ` to the standard basis vectors. -/
private theorem linearIndependent_coords_comp :
    LinearIndependent R (D.coords ∘ Sum.elim D.e D.f) := by
  classical
  convert Pi.linearIndependent_single_one (Fin ℓ ⊕ Fin ℓ) R using 1
  funext i k
  rcases i with i | i <;> rcases k with k | k <;> simp [coords, Pi.single_apply, eq_comm]

/-- The vectors `eᵢ` and `e₋ᵢ` of a Bessel datum are linearly independent. -/
theorem linearIndependent_e_f : LinearIndependent R (Sum.elim D.e D.f) :=
  D.linearIndependent_coords_comp.of_comp

theorem linearIndependent_e : LinearIndependent R D.e :=
  D.linearIndependent_e_f.comp _ Sum.inl_injective

theorem linearIndependent_f : LinearIndependent R D.f :=
  D.linearIndependent_e_f.comp _ Sum.inr_injective

/-- The span of the vectors `e₋ℓ, …, e₋₁, e₁, …, e_ℓ` of a Bessel datum and its middle space are
complementary: `V = ⟨e₋ℓ, …, e_ℓ⟩ ⊕ V_ℓ`. -/
theorem isCompl_span_middleSpace :
    IsCompl (Submodule.span R (Set.range D.e ∪ Set.range D.f)) D.middleSpace := by
  classical
  -- The pairings with `e₋ₖ` and `eₖ` form a family of forms biorthogonal to the `eᵢ`, `e₋ᵢ`.
  have h := Submodule.isCompl_span_range_iInf_ker_of_apply_eq_ite (v := Sum.elim D.e D.f)
    (f := Sum.elim (fun k ↦ associated Q (D.f k)) fun k ↦ associated Q (D.e k))
    (by rintro (i | i) (k | k) <;> simp [eq_comm])
  rw [Set.Sum.elim_range] at h
  convert h using 1
  ext x
  simp [Submodule.mem_iInf, Sum.forall, and_comm]

/-- The middle space of a Bessel datum in a regular quadratic space is regular. -/
theorem nondegenerate_restrict_middleSpace (hQ : Q.Nondegenerate) :
    (Q.restrict D.middleSpace).Nondegenerate := by
  rw [← nondegenerate_associated_iff] at hQ ⊢
  -- `associated (Q.restrict W)` is definitionally `(associated Q).restrict W`.
  exact LinearMap.BilinForm.nondegenerate_restrict_orthogonal_of_isCompl
    (QuadraticForm.associated_isSymm R Q).isRefl hQ D.isCompl_span_middleSpace

/-! ### Transport along isometries -/

/-- An isometry carries a Bessel datum of index `ℓ` to a Bessel datum of index `ℓ`. -/
def map {Q' : QuadraticForm R N} (φ : Q →qᵢ Q') : OrthogonalBesselDatum Q' ℓ where
  e i := φ (D.e i)
  f i := φ (D.f i)
  w := φ D.w
  associated_e_e i k := by rw [φ.associated_apply, D.associated_e_e]
  associated_f_f i k := by rw [φ.associated_apply, D.associated_f_f]
  associated_e_f i k := by rw [φ.associated_apply, D.associated_e_f]
  associated_e_w i := by rw [φ.associated_apply, D.associated_e_w]
  associated_f_w i := by rw [φ.associated_apply, D.associated_f_w]
  apply_w_ne_zero := by rw [φ.map_app]; exact D.apply_w_ne_zero

@[simp]
theorem map_e {Q' : QuadraticForm R N} (φ : Q →qᵢ Q') (i : Fin ℓ) :
    (D.map φ).e i = φ (D.e i) := (rfl)

@[simp]
theorem map_f {Q' : QuadraticForm R N} (φ : Q →qᵢ Q') (i : Fin ℓ) :
    (D.map φ).f i = φ (D.f i) := (rfl)

@[simp]
theorem map_w {Q' : QuadraticForm R N} (φ : Q →qᵢ Q') : (D.map φ).w = φ D.w := (rfl)

@[simp]
theorem map_id : D.map (Isometry.id Q) = D := (rfl)

theorem map_comp {P : Type*} [AddCommGroup P] [Module R P] {Q' : QuadraticForm R N}
    {Q'' : QuadraticForm R P} (ψ : Q' →qᵢ Q'') (φ : Q →qᵢ Q') :
    D.map (ψ.comp φ) = (D.map φ).map ψ := (rfl)

theorem flag_map {Q' : QuadraticForm R N} (φ : Q →qᵢ Q') (j : ℕ) :
    (D.map φ).flag j = (D.flag j).map φ.toLinearMap := by
  rw [flag, flag, Submodule.map_span, ← Set.image_comp]
  exact congrArg (Submodule.span R) (Set.image_congr fun i _ ↦ D.map_e φ i)

/-! ### Extension of scalars -/

/-- Extending scalars along a faithful algebra carries a Bessel datum of index `ℓ` for `Q` to a
Bessel datum of index `ℓ` for the base change of `Q`, with vectors `1 ⊗ₜ eᵢ`, `1 ⊗ₜ e₋ᵢ` and
`1 ⊗ₜ w`. -/
noncomputable def baseChange (A : Type*) [CommRing A] [Algebra R A] [Invertible (2 : A)]
    [FaithfulSMul R A] : OrthogonalBesselDatum (Q.baseChange A) ℓ where
  e i := 1 ⊗ₜ D.e i
  f i := 1 ⊗ₜ D.f i
  w := 1 ⊗ₜ D.w
  associated_e_e i k := by simp [QuadraticForm.associated_baseChange]
  associated_f_f i k := by simp [QuadraticForm.associated_baseChange]
  associated_e_f i k := by split_ifs <;> simp [QuadraticForm.associated_baseChange, *]
  associated_e_w i := by simp [QuadraticForm.associated_baseChange]
  associated_f_w i := by simp [QuadraticForm.associated_baseChange]
  apply_w_ne_zero := by
    rw [QuadraticForm.baseChange_one_tmul, ne_eq,
      map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective R A)]
    exact D.apply_w_ne_zero

section BaseChange

variable (A : Type*) [CommRing A] [Algebra R A] [Invertible (2 : A)] [FaithfulSMul R A]

@[simp]
theorem baseChange_e (i : Fin ℓ) : (D.baseChange A).e i = 1 ⊗ₜ D.e i := (rfl)

@[simp]
theorem baseChange_f (i : Fin ℓ) : (D.baseChange A).f i = 1 ⊗ₜ D.f i := (rfl)

@[simp]
theorem baseChange_w : (D.baseChange A).w = 1 ⊗ₜ D.w := (rfl)

/-- The flag of the base-changed datum is the base change of the flag. -/
theorem flag_baseChange (j : ℕ) : (D.baseChange A).flag j = (D.flag j).baseChange A := by
  simp only [flag, Submodule.baseChange_span, Set.image_image, baseChange_e, TensorProduct.mk_apply]

end BaseChange

end CommRing

/-! ### Linear independence and dimensions -/

section Field

variable {K : Type u} {V : Type v} [Field K] [Invertible (2 : K)] [AddCommGroup V] [Module K V]
  {Q : QuadraticForm K V} {ℓ : ℕ} (D : OrthogonalBesselDatum Q ℓ)

/-- The vectors `eᵢ`, `e₋ᵢ` and `w` of a Bessel datum are linearly independent. -/
theorem linearIndependent :
    LinearIndependent K (Sum.elim (Sum.elim D.e D.f) fun _ : Unit ↦ D.w) := by
  -- `w` is a nonzero vector of the middle space, which meets the span of the `e±ᵢ` trivially.
  refine D.linearIndependent_e_f.sum_type (linearIndependent_unique_iff.mpr D.w_ne_zero) ?_
  rw [Set.Sum.elim_range]
  refine D.isCompl_span_middleSpace.disjoint.mono_right (Submodule.span_le.mpr ?_)
  rintro _ ⟨_, rfl⟩
  exact D.w_mem_middleSpace

/-- The `j`-th subspace of the flag has dimension `j` for `j ≤ ℓ`. -/
theorem finrank_flag {j : ℕ} (hj : j ≤ ℓ) : finrank K (D.flag j) = j := by
  classical
  rw [flag, Set.image_eq_range]
  refine (finrank_span_eq_card (b := fun i : {i : Fin ℓ | (i : ℕ) < j} ↦ D.e i)
    (D.linearIndependent_e.comp _ Subtype.val_injective)).trans ?_
  simp [Fintype.card_subtype, Fin.card_filter_val_lt, hj]

include D in
/-- The index of a Bessel datum in a regular space is at most the Witt index. -/
theorem le_wittIndex [FiniteDimensional K V] (hQ : Q.Nondegenerate) :
    ℓ ≤ RegularFormClass.wittIndex (formClass Q hQ) :=
  D.finrank_flag le_rfl ▸ (D.isTotallyIsotropic_flag ℓ).finrank_le_wittIndex hQ

include D in
/-- A Bessel datum of index `ℓ` lives in a space of dimension at least `2ℓ + 1`. -/
theorem two_mul_add_one_le_finrank [FiniteDimensional K V] : 2 * ℓ + 1 ≤ finrank K V := by
  simpa [two_mul] using D.linearIndependent.fintype_card_le_finrank

/-- The middle space of a Bessel datum of index `ℓ` has codimension `2ℓ`. -/
theorem finrank_middleSpace [FiniteDimensional K V] :
    finrank K D.middleSpace + 2 * ℓ = finrank K V := by
  have hspan : finrank K (Submodule.span K (Set.range D.e ∪ Set.range D.f)) = 2 * ℓ := by
    rw [← Set.Sum.elim_range, finrank_span_eq_card D.linearIndependent_e_f]
    simp [two_mul]
  rw [← hspan, add_comm, Submodule.finrank_add_eq_of_isCompl D.isCompl_span_middleSpace]

end Field

/-! ### Existence -/

section Existence

variable {K : Type u} [Field K] [Invertible (2 : K)]

/-- Adjoin a hyperbolic pair `(x, y)`, normalized by `associated Q x y = 1`, to a Bessel datum all
of whose vectors are orthogonal to `x` and `y`, as the new first pair `(e₁, e₋₁)`. -/
private def cons {V : Type v} [AddCommGroup V] [Module K V] {Q : QuadraticForm K V} {ℓ : ℕ}
    (D : OrthogonalBesselDatum Q ℓ) {x y : V} (hx : Q x = 0) (hy : Q y = 0)
    (hxy : associated Q x y = 1)
    (hD : ∀ v ∈ Set.range D.e ∪ Set.range D.f ∪ {D.w},
      associated Q x v = 0 ∧ associated Q y v = 0) :
    OrthogonalBesselDatum Q (ℓ + 1) := by
  have he i := hD (D.e i) (Or.inl (Or.inl ⟨i, rfl⟩))
  have hf i := hD (D.f i) (Or.inl (Or.inr ⟨i, rfl⟩))
  have hw := hD D.w (Or.inr rfl)
  have hxx : associated Q x x = 0 := by rw [associated_eq_self_apply, hx]
  have hyy : associated Q y y = 0 := by rw [associated_eq_self_apply, hy]
  exact
  { e := Fin.cons x D.e
    f := Fin.cons y D.f
    w := D.w
    associated_e_e := fun i k ↦ by
      refine Fin.cases ?_ (fun i ↦ ?_) i <;> refine Fin.cases ?_ (fun k ↦ ?_) k <;>
        simp [hxx, (he _).1, associated_isSymm K Q (D.e _) x]
    associated_f_f := fun i k ↦ by
      refine Fin.cases ?_ (fun i ↦ ?_) i <;> refine Fin.cases ?_ (fun k ↦ ?_) k <;>
        simp [hyy, (hf _).2, associated_isSymm K Q (D.f _) y]
    associated_e_f := fun i k ↦ by
      refine Fin.cases ?_ (fun i ↦ ?_) i <;> refine Fin.cases ?_ (fun k ↦ ?_) k <;>
        simp [hxy, (hf _).1, (he _).2, associated_isSymm K Q (D.e _) y,
          (Fin.succ_ne_zero _).symm]
    associated_e_w := fun i ↦ by
      refine Fin.cases ?_ (fun i ↦ ?_) i <;> simp [hw.1]
    associated_f_w := fun i ↦ by
      refine Fin.cases ?_ (fun i ↦ ?_) i <;> simp [hw.2]
    apply_w_ne_zero := D.apply_w_ne_zero }

/-- The converse direction of `nonempty_iff`, by splitting off hyperbolic planes one at a time. -/
private theorem nonempty_of_le : ∀ (ℓ : ℕ) {V : Type v} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (Q : QuadraticForm K V) (hQ : Q.Nondegenerate),
    ℓ ≤ RegularFormClass.wittIndex (formClass Q hQ) → 2 * ℓ + 1 ≤ finrank K V →
      Nonempty (OrthogonalBesselDatum Q ℓ)
  | 0, V, _, _, _, Q, hQ, _, hd => by
    have : Nontrivial V := (Module.finrank_pos_iff (R := K)).mp (by omega)
    obtain ⟨w, hw⟩ : ∃ w, Q w ≠ 0 := not_forall.mp fun h ↦ hQ.ne_zero (QuadraticMap.ext h)
    exact ⟨⟨Fin.elim0, Fin.elim0, w, nofun, nofun, nofun, nofun, nofun, hw⟩⟩
  | ℓ + 1, V, _, _, _, Q, hQ, hr, hd => by
    have hiso : ¬Q.Anisotropic := by
      rw [← QuadraticForm.anisotropic_formClass Q hQ, ← RegularFormClass.wittIndex_eq_zero_iff]
      omega
    obtain ⟨x, y, -, hx, hy, hxy⟩ := exists_isotropic_pair_of_radical_eq_bot hQ.radical_eq_bot hiso
    set U := LinearMap.BilinForm.orthogonal (polarBilin Q) (Submodule.span K {x, y})
    have hU := hQ.nondegenerate_restrict_orthogonal_span_pair hx hy hxy
    have hindex : RegularFormClass.wittIndex (formClass Q hQ) =
        RegularFormClass.wittIndex (formClass (Q.restrict U) hU) + 1 :=
      (Q.wittIndex_formClass_restrict_orthogonal_span_pair_add_one hQ hx hy hxy).symm
    have hdim : finrank K V = finrank K U + 2 :=
      (Q.finrank_orthogonal_span_pair_add_two hx hy hxy).symm
    obtain ⟨D⟩ := nonempty_of_le ℓ (Q.restrict U) hU (by omega) (by omega)
    -- Every vector of `U` is orthogonal to `x` and to `y`; rescale `y` to `B x y = 1`.
    have hUxy (u : U) : associated Q x u = 0 ∧ associated Q ((2 : K) • y) u = 0 := by
      have h := LinearMap.BilinForm.mem_orthogonal_iff.mp u.property
      have hx' := h x (Submodule.subset_span (by simp))
      have hy' := h y (Submodule.subset_span (by simp))
      simp only [polarBilin_apply_apply, polar_eq_two_nsmul_associated, two_nsmul, ← two_mul,
        (isUnit_of_invertible (2 : K)).mul_right_eq_zero] at hx' hy'
      simp [hx', hy']
    have hxy' : associated Q x ((2 : K) • y) = 1 := by
      rw [map_smul, smul_eq_mul, two_mul, ← two_nsmul, ← polar_eq_two_nsmul_associated, hxy]
    refine ⟨cons (D.map ⟨U.subtype, fun _ ↦ rfl⟩) (y := (2 : K) • y) hx
      (by rw [QuadraticMap.map_smul, hy, smul_zero]) hxy' ?_⟩
    rintro _ ((⟨i, rfl⟩ | ⟨i, rfl⟩) | rfl) <;> exact hUxy _

/-- **Existence of Bessel data.** Over a field in which `2` is invertible, a regular quadratic
space of dimension `d` and Witt index `r` carries an orthogonal Bessel datum of index `ℓ` exactly
when `ℓ ≤ r` and `2ℓ + 1 ≤ d`. -/
theorem nonempty_iff {V : Type v} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {Q : QuadraticForm K V} (hQ : Q.Nondegenerate) {ℓ : ℕ} :
    Nonempty (OrthogonalBesselDatum Q ℓ) ↔
      ℓ ≤ RegularFormClass.wittIndex (formClass Q hQ) ∧ 2 * ℓ + 1 ≤ finrank K V :=
  ⟨fun ⟨D⟩ ↦ ⟨D.le_wittIndex hQ, D.two_mul_add_one_le_finrank⟩,
    fun h ↦ nonempty_of_le ℓ Q hQ h.1 h.2⟩

end Existence

end OrthogonalBesselDatum

end TauCeti
