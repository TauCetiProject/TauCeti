/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecificLimits.Basic
public import TauCeti.Analysis.CStarAlgebra.BoundedProduct
public import TauCeti.Analysis.CStarAlgebra.Quotient
public import TauCeti.Analysis.Normed.Lp.C0Ideal
public import TauCeti.Analysis.Normed.Lp.Reindex

/-!
# Norm sequence algebras and C⋆-ultrapowers

For any (possibly non-unital) C⋆-algebra `A` and filter `l : Filter ι`, the filter-null ideal
`lp.nullIdeal (fun _ : ι ↦ A) l` of `lp (fun _ : ι ↦ A) ∞` is closed (`lp.isClosed_nullIdeal`), so
`TauCeti.CStarFilterQuotient A l := lp (fun _ : ι ↦ A) ∞ ⧸ lp.nullIdeal (fun _ : ι ↦ A) l`
is a C⋆-algebra (unital whenever `A` is unital and nontrivial, and nontrivial whenever both `A` and
`l` are nontrivial). Specializing `l` yields:

* `TauCeti.CStarSequenceAlgebra A := CStarFilterQuotient A (atTop : Filter ℕ)`, the **norm sequence
  algebra** `A_∞ = ℓ^∞(ℕ, A) / c₀(ℕ, A)`, with quotient norm `‖[a]‖ = limsup_{n → ∞} ‖a n‖`;
* `TauCeti.CStarUltrapower A ω := CStarFilterQuotient A (ω : Filter ι)` for `ω : Ultrafilter ι`, the
  **norm C⋆-ultrapower** `A_ω = ℓ^∞(ι, A) / c_ω(ι, A)`, with ultralimit norm `‖[a]‖ = lim_ω ‖a i‖`.

We establish norm-attaining bounded representatives, isometric diagonal embeddings, functoriality
under `⋆`-homomorphisms and `⋆`-equivalences, quotient maps between comparable filters, diagonal
reindexing along `Tendsto r l' l`, the asymptotic-commutator characterization of relative commutants
(covering both `A_ω ∩ A′` and `M(A)_ω ∩ A′`), and the parity-indicator separation between `A_∞` and
`A_ω`.

## References

* E. Kirchberg, N. C. Phillips, *Embedding of exact C⋆-algebras in the Cuntz algebra `𝒪₂`*,
  Lemma 2.2.
* M. Rørdam, *Classification of Nuclear, Simple C⋆-Algebras*, Chapter 6.
* B. Blackadar, *Operator Algebras*, II.8.1.
-/

public section

open Filter Topology
open scoped ENNReal CStarAlgebra

namespace TauCeti

noncomputable section

/-- The C⋆-algebra of bounded `ι`-indexed families in `A` modulo those whose coordinate norms tend
to `0` along `l : Filter ι`. -/
abbrev CStarFilterQuotient (A : Type*) [NonUnitalNormedRing A] {ι : Type*} (l : Filter ι) :
    Type _ := lp (fun _ : ι ↦ A) ∞ ⧸ lp.nullIdeal (fun _ : ι ↦ A) l

/-- The norm sequence algebra `A_∞ = ℓ^∞(ℕ, A) / c₀(ℕ, A)` of a C⋆-algebra `A`. -/
abbrev CStarSequenceAlgebra (A : Type*) [NonUnitalNormedRing A] : Type _ :=
  CStarFilterQuotient A (atTop : Filter ℕ)

/-- The norm C⋆-ultrapower `A_ω = ℓ^∞(ι, A) / c_ω(ι, A)` of a C⋆-algebra `A` along an ultrafilter
`ω : Ultrafilter ι`. -/
abbrev CStarUltrapower (A : Type*) [NonUnitalNormedRing A] {ι : Type*} (ω : Ultrafilter ι) :
    Type _ := CStarFilterQuotient A (ω : Filter ι)

namespace CStarFilterQuotient

section NonUnital

variable {ι ι' : Type*} {A B : Type*} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]

variable (A) in
/-- The canonical quotient `⋆`-homomorphism `ℓ^∞(ι, A) →⋆ₙₐ[ℂ] CStarFilterQuotient A l`. -/
def mk (l : Filter ι) : lp (fun _ : ι ↦ A) ∞ →⋆ₙₐ[ℂ] CStarFilterQuotient A l :=
  TwoSidedIdeal.Quotient.mkStarAlgHom (lp.nullIdeal (fun _ : ι ↦ A) l)

theorem mk_apply (l : Filter ι) (a : lp (fun _ : ι ↦ A) ∞) :
    mk A l a = TwoSidedIdeal.Quotient.mk (lp.nullIdeal (fun _ : ι ↦ A) l) a :=
  TwoSidedIdeal.Quotient.mkStarAlgHom_apply _ a

theorem mk_surjective (l : Filter ι) : Function.Surjective (mk A l) :=
  TwoSidedIdeal.Quotient.mkStarAlgHom_surjective _

@[simp]
theorem mk_eq_zero_iff {l : Filter ι} {a : lp (fun _ : ι ↦ A) ∞} :
    mk A l a = 0 ↔ Tendsto (fun i ↦ ‖a i‖) l (𝓝 0) := by
  rw [mk_apply, TwoSidedIdeal.Quotient.eq_zero_iff_mem, lp.mem_nullIdeal]

theorem mk_eq_mk_iff {l : Filter ι} {a b : lp (fun _ : ι ↦ A) ∞} :
    mk A l a = mk A l b ↔ Tendsto (fun i ↦ ‖a i - b i‖) l (𝓝 0) := by
  rw [mk_apply, mk_apply, lp.mk_nullIdeal_eq_mk_iff]

/-- **Quotient norm formula.** For any filter `l`, `‖mk A l a‖ = limsup_i ‖a i‖` along `l`. -/
theorem norm_mk {l : Filter ι} (a : lp (fun _ : ι ↦ A) ∞) :
    ‖mk A l a‖ = limsup (fun i ↦ ‖a i‖) l := by rw [mk_apply]; exact lp.norm_mk_nullIdeal a

theorem norm_mk_le (l : Filter ι) (a : lp (fun _ : ι ↦ A) ∞) : ‖mk A l a‖ ≤ ‖a‖ := by
  rw [mk_apply]; exact TwoSidedIdeal.Quotient.norm_mk_le _ a

/-- If `‖mk A l a‖ < ε`, then `‖a i‖ < ε` eventually along `l`. -/
theorem eventually_norm_lt_of_norm_mk_lt {l : Filter ι} (a : lp (fun _ : ι ↦ A) ∞) {ε : ℝ}
    (ha : ‖mk A l a‖ < ε) : ∀ᶠ i in l, ‖a i‖ < ε := by
  rw [mk_apply] at ha; exact lp.eventually_norm_lt_of_norm_mk_nullIdeal_lt a ha

/-- **Bounded norm-attaining representative.** Every element `x : CStarFilterQuotient A l` lifts to
a bounded family `a : lp (fun _ : ι ↦ A) ∞` with `‖a‖ = ‖x‖`. -/
theorem exists_mk_eq_and_norm_eq (l : Filter ι) (x : CStarFilterQuotient A l) :
    ∃ a : lp (fun _ : ι ↦ A) ∞, mk A l a = x ∧ ‖a‖ = ‖x‖ := by
  simpa only [mk_apply] using lp.exists_mk_nullIdeal_eq_and_norm_eq l x

variable (A) in
/-- The diagonal embedding `A →⋆ₙₐ[ℂ] CStarFilterQuotient A l` sending `a` to the class of the
constant family `fun _ ↦ a`. -/
def diag (l : Filter ι) : A →⋆ₙₐ[ℂ] CStarFilterQuotient A l :=
  (mk A l).comp (lp.constNonUnitalStarAlgHom ℂ ι A)

theorem diag_eq_mk_const (l : Filter ι) (a : A) :
    diag A l a = mk A l (lp.constNonUnitalStarAlgHom ℂ ι A a) := (rfl)

@[simp]
theorem norm_diag {l : Filter ι} [l.NeBot] (a : A) : ‖diag A l a‖ = ‖a‖ := by
  rw [diag_eq_mk_const, norm_mk]; simp

/-- The diagonal embedding `diag A l` is an isometry whenever `l` is nontrivial. -/
theorem isometry_diag (l : Filter ι) [l.NeBot] : Isometry (diag A l) :=
  AddMonoidHomClass.isometry_of_norm _ norm_diag

/-- The diagonal embedding `diag A l` is injective whenever `l` is nontrivial. -/
theorem diag_injective (l : Filter ι) [l.NeBot] : Function.Injective (diag A l) :=
  (isometry_diag l).injective

/-- `CStarFilterQuotient A l` is nontrivial whenever `A` and `l` are nontrivial. -/
instance nontrivial [Nontrivial A] {l : Filter ι} [l.NeBot] :
    Nontrivial (CStarFilterQuotient A l) := (diag_injective (A := A) l).nontrivial

/-- Functoriality of `CStarFilterQuotient` along a non-unital `⋆`-homomorphism `φ : A →⋆ₙₐ[ℂ] B`. -/
def map (l : Filter ι) (φ : A →⋆ₙₐ[ℂ] B) :
    CStarFilterQuotient A l →⋆ₙₐ[ℂ] CStarFilterQuotient B l :=
  TwoSidedIdeal.Quotient.liftStarAlgHom (lp.nullIdeal (fun _ : ι ↦ A) l)
    ((mk B l).comp (lp.mapNonUnitalStarAlgHom fun _ ↦ φ)) fun a ha ↦ by
      rw [NonUnitalStarAlgHom.comp_apply, mk_eq_zero_iff]
      exact squeeze_zero (fun _ ↦ norm_nonneg _)
        (fun i ↦ by
          rw [lp.mapNonUnitalStarAlgHom_apply]; exact NonUnitalStarAlgHom.norm_apply_le φ (a i))
        (lp.mem_nullIdeal.mp ha)

@[simp]
theorem map_mk (l : Filter ι) (φ : A →⋆ₙₐ[ℂ] B) (a : lp (fun _ : ι ↦ A) ∞) :
    map l φ (mk A l a) = mk B l (lp.mapNonUnitalStarAlgHom (fun _ ↦ φ) a) := by
  rw [mk_apply]; exact TwoSidedIdeal.Quotient.liftStarAlgHom_mk _ _ _ a

@[simp]
theorem map_comp_diag (l : Filter ι) (φ : A →⋆ₙₐ[ℂ] B) :
    (map l φ).comp (diag A l) = (diag B l).comp φ := by
  ext a; simp only [NonUnitalStarAlgHom.comp_apply, diag_eq_mk_const, map_mk]; congr 1; ext; simp

@[simp]
theorem map_diag (l : Filter ι) (φ : A →⋆ₙₐ[ℂ] B) (a : A) :
    map l φ (diag A l a) = diag B l (φ a) := DFunLike.congr_fun (map_comp_diag l φ) a

@[simp]
theorem map_id (l : Filter ι) :
    map l (NonUnitalStarAlgHom.id ℂ A) = NonUnitalStarAlgHom.id ℂ (CStarFilterQuotient A l) :=
  NonUnitalStarAlgHom.ext fun x ↦ by obtain ⟨a, rfl⟩ := mk_surjective l x; simp

theorem map_comp {C : Type*} [NonUnitalCStarAlgebra C] (l : Filter ι) (ψ : B →⋆ₙₐ[ℂ] C)
    (φ : A →⋆ₙₐ[ℂ] B) : (map l ψ).comp (map l φ) = map l (ψ.comp φ) :=
  NonUnitalStarAlgHom.ext fun x ↦ by
    obtain ⟨a, rfl⟩ := mk_surjective l x
    simp only [NonUnitalStarAlgHom.comp_apply, map_mk]; congr 1; ext; simp

/-- An injective `⋆`-homomorphism induces an injective map on `CStarFilterQuotient`. -/
theorem map_injective_of_injective (l : Filter ι) {φ : A →⋆ₙₐ[ℂ] B}
    (hφ : Function.Injective φ) : Function.Injective (map l φ) := by
  refine TwoSidedIdeal.Quotient.liftStarAlgHom_injective_of_ker_le _ fun a ha ↦ ?_
  rw [TwoSidedIdeal.mem_ker, NonUnitalStarAlgHom.comp_apply, mk_eq_zero_iff] at ha
  exact lp.mem_nullIdeal.mpr (by simpa [NonUnitalStarAlgHom.norm_map φ hφ] using ha)

/-- An injective `⋆`-homomorphism induces an isometric map on `CStarFilterQuotient`. -/
theorem isometry_map (l : Filter ι) {φ : A →⋆ₙₐ[ℂ] B} (hφ : Function.Injective φ) :
    Isometry (map l φ) := NonUnitalStarAlgHom.isometry _ (map_injective_of_injective l hφ)

/-- Functorial `⋆`-isomorphism on `CStarFilterQuotient` induced by `e : A ≃⋆ₐ[ℂ] B`. -/
def mapEquiv (l : Filter ι) (e : A ≃⋆ₐ[ℂ] B) :
    CStarFilterQuotient A l ≃⋆ₐ[ℂ] CStarFilterQuotient B l :=
  StarAlgEquiv.ofNonUnitalStarAlgHom (map l e.toNonUnitalStarAlgHom)
    (map l e.symm.toNonUnitalStarAlgHom)
    (by rw [map_comp, ← map_id (A := A) l]; congr 1; ext; simp)
    (by rw [map_comp, ← map_id (A := B) l]; congr 1; ext; simp)

@[simp]
theorem toNonUnitalStarAlgHom_mapEquiv (l : Filter ι) (e : A ≃⋆ₐ[ℂ] B) :
    (mapEquiv l e).toNonUnitalStarAlgHom = map l e.toNonUnitalStarAlgHom :=
  StarAlgEquiv.toNonUnitalStarAlgHom_ofNonUnitalStarAlgHom _ _ _ _

@[simp]
theorem mapEquiv_mk (l : Filter ι) (e : A ≃⋆ₐ[ℂ] B) (a : lp (fun _ : ι ↦ A) ∞) :
    mapEquiv l e (mk A l a) =
      mk B l (lp.mapNonUnitalStarAlgHom (fun _ ↦ e.toNonUnitalStarAlgHom) a) :=
  map_mk l e.toNonUnitalStarAlgHom a

@[simp]
theorem mapEquiv_diag (l : Filter ι) (e : A ≃⋆ₐ[ℂ] B) (a : A) :
    mapEquiv l e (diag A l a) = diag B l (e a) := by
  rw [← StarAlgEquiv.toNonUnitalStarAlgHom_apply, toNonUnitalStarAlgHom_mapEquiv, map_diag,
    StarAlgEquiv.toNonUnitalStarAlgHom_apply]

@[simp]
theorem mapEquiv_symm (l : Filter ι) (e : A ≃⋆ₐ[ℂ] B) :
    (mapEquiv l e).symm = mapEquiv l e.symm := (rfl)

variable (A) in
/-- Canonical surjective quotient `⋆`-homomorphism when passing to a finer filter `l' ≤ l`. -/
def factor {l l' : Filter ι} (h : l' ≤ l) :
    CStarFilterQuotient A l →⋆ₙₐ[ℂ] CStarFilterQuotient A l' :=
  TwoSidedIdeal.Quotient.factorStarAlgHom (lp.nullIdeal_antitone (A := fun _ : ι ↦ A) h)

@[simp]
theorem factor_mk {l l' : Filter ι} (h : l' ≤ l) (a : lp (fun _ : ι ↦ A) ∞) :
    factor A h (mk A l a) = mk A l' a := by
  rw [mk_apply, mk_apply, factor]
  exact TwoSidedIdeal.Quotient.factorStarAlgHom_mk (lp.nullIdeal_antitone (A := fun _ : ι ↦ A) h) a

/-- Passing to a finer filter `l' ≤ l` gives a surjective quotient map on `CStarFilterQuotient`. -/
theorem factor_surjective {l l' : Filter ι} (h : l' ≤ l) : Function.Surjective (factor A h) :=
  TwoSidedIdeal.Quotient.factorStarAlgHom_surjective (lp.nullIdeal_antitone (A := fun _ : ι ↦ A) h)

@[simp]
theorem factor_comp_diag {l l' : Filter ι} (h : l' ≤ l) :
    (factor A h).comp (diag A l) = diag A l' :=
  NonUnitalStarAlgHom.ext fun a ↦ by simp [diag_eq_mk_const]

@[simp]
theorem factor_diag {l l' : Filter ι} (h : l' ≤ l) (a : A) :
    factor A h (diag A l a) = diag A l' a :=
  DFunLike.congr_fun (factor_comp_diag (A := A) h) a

@[simp]
theorem factor_refl (l : Filter ι) :
    factor A (le_refl l) = NonUnitalStarAlgHom.id ℂ (CStarFilterQuotient A l) :=
  TwoSidedIdeal.Quotient.factorStarAlgHom_refl

theorem factor_trans {l₁ l₂ l₃ : Filter ι} (h₂₃ : l₃ ≤ l₂) (h₁₂ : l₂ ≤ l₁) :
    (factor A h₂₃).comp (factor A h₁₂) = factor A (h₂₃.trans h₁₂) :=
  TwoSidedIdeal.Quotient.factorStarAlgHom_comp _ _

variable (A) in
/-- Reindexing `a ↦ a ∘ r` descends to `CStarFilterQuotient A l →⋆ₙₐ[ℂ] CStarFilterQuotient A l'`
whenever `Tendsto r l' l`, and fixes the diagonal subalgebra. -/
def reindex {l : Filter ι} {l' : Filter ι'} {r : ι' → ι} (hr : Tendsto r l' l) :
    CStarFilterQuotient A l →⋆ₙₐ[ℂ] CStarFilterQuotient A l' :=
  TwoSidedIdeal.Quotient.liftStarAlgHom (lp.nullIdeal (fun _ : ι ↦ A) l)
    ((mk A l').comp (lp.reindexNonUnitalStarAlgHom ℂ A r)) fun a ha ↦ by
      rw [NonUnitalStarAlgHom.comp_apply, mk_eq_zero_iff]
      simpa only [Function.comp_def, lp.reindexNonUnitalStarAlgHom_apply] using
        (lp.mem_nullIdeal.mp ha).comp hr

@[simp]
theorem reindex_mk {l : Filter ι} {l' : Filter ι'} {r : ι' → ι} (hr : Tendsto r l' l)
    (a : lp (fun _ : ι ↦ A) ∞) :
    reindex A hr (mk A l a) = mk A l' (lp.reindexNonUnitalStarAlgHom ℂ A r a) := by
  rw [mk_apply]; exact TwoSidedIdeal.Quotient.liftStarAlgHom_mk _ _ _ a

@[simp]
theorem reindex_comp_diag {l : Filter ι} {l' : Filter ι'} {r : ι' → ι} (hr : Tendsto r l' l) :
    (reindex A hr).comp (diag A l) = diag A l' :=
  NonUnitalStarAlgHom.ext fun a ↦ by
    simp only [NonUnitalStarAlgHom.comp_apply, diag_eq_mk_const, reindex_mk]; congr 1; ext; simp

@[simp]
theorem reindex_diag {l : Filter ι} {l' : Filter ι'} {r : ι' → ι} (hr : Tendsto r l' l) (a : A) :
    reindex A hr (diag A l a) = diag A l' a :=
  DFunLike.congr_fun (reindex_comp_diag (A := A) hr) a

@[simp]
theorem reindex_id (l : Filter ι) :
    reindex A (tendsto_id : Tendsto id l l) =
      NonUnitalStarAlgHom.id ℂ (CStarFilterQuotient A l) :=
  NonUnitalStarAlgHom.ext fun x ↦ by obtain ⟨a, rfl⟩ := mk_surjective l x; simp

theorem reindex_comp {ι'' : Type*} {l : Filter ι} {l' : Filter ι'} {l'' : Filter ι''}
    {r : ι' → ι} {s : ι'' → ι'} (hs : Tendsto s l'' l') (hr : Tendsto r l' l) :
    (reindex A hs).comp (reindex A hr) = reindex A (hr.comp hs) :=
  NonUnitalStarAlgHom.ext fun x ↦ by
    obtain ⟨a, rfl⟩ := mk_surjective l x
    rw [NonUnitalStarAlgHom.comp_apply, reindex_mk, reindex_mk, reindex_mk,
      ← lp.reindexNonUnitalStarAlgHom_comp, NonUnitalStarAlgHom.comp_apply]

/-- **Asymptotic-commutator characterization of relative commutants.** Given a `⋆`-homomorphism
`φ : C → A`, the class `mk A l a` belongs to the relative commutant of `diag A l ∘ φ` in
`CStarFilterQuotient A l` if and only if `‖φ c * a i - a i * φ c‖ → 0` along `l` for every `c`. -/
theorem mem_centralizer_range_diag_comp_iff {F C : Type*} [Star C] [FunLike F C A]
    [StarHomClass F C A] (l : Filter ι) (φ : F) (a : lp (fun _ : ι ↦ A) ∞) :
    mk A l a ∈ NonUnitalStarSubalgebra.centralizer ℂ (Set.range fun c ↦ diag A l (φ c)) ↔
      ∀ c : C, Tendsto (fun i ↦ ‖φ c * a i - a i * φ c‖) l (𝓝 0) := by
  rw [NonUnitalStarSubalgebra.mem_centralizer_iff]
  constructor
  · intro h c
    have hc := (h (diag A l (φ c)) ⟨c, rfl⟩).left
    rw [diag_eq_mk_const, ← map_mul, ← map_mul, mk_eq_mk_iff] at hc
    simpa only [lp.infty_coeFn_mul, Pi.mul_apply, lp.constNonUnitalStarAlgHom_apply] using hc
  · rintro h _ ⟨c, rfl⟩
    dsimp only
    refine ⟨?_, ?_⟩
    · rw [diag_eq_mk_const, ← map_mul, ← map_mul, mk_eq_mk_iff]
      simpa only [lp.infty_coeFn_mul, Pi.mul_apply, lp.constNonUnitalStarAlgHom_apply] using h c
    · rw [← map_star, ← map_star, diag_eq_mk_const, ← map_mul, ← map_mul, mk_eq_mk_iff]
      simpa only [lp.infty_coeFn_mul, Pi.mul_apply, lp.constNonUnitalStarAlgHom_apply] using
        h (star c)

/-- Special case `φ = id`: `mk A l a` belongs to the central sequence algebra
`CStarFilterQuotient A l ∩ A′` if and only if `‖b * a i - a i * b‖ → 0` along `l` for every `b`. -/
theorem mem_centralizer_range_diag_iff (l : Filter ι) (a : lp (fun _ : ι ↦ A) ∞) :
    mk A l a ∈ NonUnitalStarSubalgebra.centralizer ℂ (Set.range (diag A l)) ↔
      ∀ b : A, Tendsto (fun i ↦ ‖b * a i - a i * b‖) l (𝓝 0) :=
  mem_centralizer_range_diag_comp_iff l (NonUnitalStarAlgHom.id ℂ A) a

end NonUnital

section Unital

variable {ι ι' : Type*} {A B : Type*} [CStarAlgebra A] [Nontrivial A]
  [CStarAlgebra B] [Nontrivial B]

private theorem toNonUnital_comp {C D E : Type*} [Semiring C] [StarRing C] [Algebra ℂ C]
    [Semiring D] [StarRing D] [Algebra ℂ D] [Semiring E] [StarRing E] [Algebra ℂ E]
    (g : D →⋆ₐ[ℂ] E) (f : C →⋆ₐ[ℂ] D) :
    (g.comp f).toNonUnitalStarAlgHom = g.toNonUnitalStarAlgHom.comp f.toNonUnitalStarAlgHom := by
  ext; simp

variable (A) in
/-- The canonical unital quotient `⋆`-homomorphism `ℓ^∞(ι, A) →⋆ₐ[ℂ] CStarFilterQuotient A l`. -/
def unitalMk (l : Filter ι) : lp (fun _ : ι ↦ A) ∞ →⋆ₐ[ℂ] CStarFilterQuotient A l :=
  TwoSidedIdeal.Quotient.mkUnitalStarAlgHom (lp.nullIdeal (fun _ : ι ↦ A) l)

@[simp]
theorem toNonUnitalStarAlgHom_unitalMk (l : Filter ι) :
    (unitalMk A l).toNonUnitalStarAlgHom = mk A l :=
  TwoSidedIdeal.Quotient.toNonUnitalStarAlgHom_mkUnitalStarAlgHom _

@[simp low]
theorem unitalMk_apply (l : Filter ι) (a : lp (fun _ : ι ↦ A) ∞) : unitalMk A l a = mk A l a := by
  rw [← StarAlgHom.coe_toNonUnitalStarAlgHom (unitalMk A l), toNonUnitalStarAlgHom_unitalMk]; rfl

@[simp]
theorem mk_one (l : Filter ι) : mk A l 1 = 1 := by rw [← unitalMk_apply, map_one]

theorem unitalMk_surjective (l : Filter ι) : Function.Surjective (unitalMk A l) :=
  TwoSidedIdeal.Quotient.mkUnitalStarAlgHom_surjective _

variable (A) in
/-- The unital diagonal embedding `A →⋆ₐ[ℂ] CStarFilterQuotient A l`. -/
def unitalDiag (l : Filter ι) : A →⋆ₐ[ℂ] CStarFilterQuotient A l :=
  (unitalMk A l).comp (lp.constStarAlgHom ℂ ι A)

@[simp]
theorem toNonUnitalStarAlgHom_unitalDiag (l : Filter ι) :
    (unitalDiag A l).toNonUnitalStarAlgHom = diag A l := by
  rw [unitalDiag, toNonUnital_comp, toNonUnitalStarAlgHom_unitalMk,
    lp.toNonUnitalStarAlgHom_constStarAlgHom]; rfl

@[simp low]
theorem unitalDiag_apply (l : Filter ι) (a : A) : unitalDiag A l a = diag A l a := by
  rw [← StarAlgHom.coe_toNonUnitalStarAlgHom (unitalDiag A l), toNonUnitalStarAlgHom_unitalDiag]
  rfl

@[simp]
theorem diag_one (l : Filter ι) : diag A l 1 = 1 := by rw [← unitalDiag_apply, map_one]

/-- Unital functoriality of `CStarFilterQuotient` along `φ : A →⋆ₐ[ℂ] B`. -/
def unitalMap (l : Filter ι) (φ : A →⋆ₐ[ℂ] B) :
    CStarFilterQuotient A l →⋆ₐ[ℂ] CStarFilterQuotient B l :=
  TwoSidedIdeal.Quotient.liftUnitalStarAlgHom (lp.nullIdeal (fun _ : ι ↦ A) l)
    ((unitalMk B l).comp (lp.mapStarAlgHom fun _ ↦ φ)) fun a ha ↦ by
      rw [StarAlgHom.comp_apply, unitalMk_apply, mk_eq_zero_iff]
      exact squeeze_zero (fun _ ↦ norm_nonneg _)
        (fun i ↦ by rw [lp.mapStarAlgHom_apply]; exact NonUnitalStarAlgHom.norm_apply_le φ (a i))
        (lp.mem_nullIdeal.mp ha)

@[simp]
theorem toNonUnitalStarAlgHom_unitalMap (l : Filter ι) (φ : A →⋆ₐ[ℂ] B) :
    (unitalMap l φ).toNonUnitalStarAlgHom = map l φ.toNonUnitalStarAlgHom := by
  simp only [unitalMap, map, toNonUnital_comp, toNonUnitalStarAlgHom_unitalMk,
    lp.toNonUnitalStarAlgHom_mapStarAlgHom,
    TwoSidedIdeal.Quotient.toNonUnitalStarAlgHom_liftUnitalStarAlgHom]; rfl

@[simp low]
theorem unitalMap_apply (l : Filter ι) (φ : A →⋆ₐ[ℂ] B) (x : CStarFilterQuotient A l) :
    unitalMap l φ x = map l φ.toNonUnitalStarAlgHom x := by
  rw [← StarAlgHom.coe_toNonUnitalStarAlgHom (unitalMap l φ), toNonUnitalStarAlgHom_unitalMap]; rfl

@[simp]
theorem unitalMap_comp_unitalDiag (l : Filter ι) (φ : A →⋆ₐ[ℂ] B) :
    (unitalMap l φ).comp (unitalDiag A l) = (unitalDiag B l).comp φ := by ext; simp

@[simp]
theorem unitalMap_id (l : Filter ι) :
    unitalMap l (StarAlgHom.id ℂ A) = StarAlgHom.id ℂ (CStarFilterQuotient A l) := by
  have hid : (StarAlgHom.id ℂ A).toNonUnitalStarAlgHom = .id ℂ A := rfl
  ext; simp [hid]

theorem unitalMap_comp {C : Type*} [CStarAlgebra C] [Nontrivial C] (l : Filter ι)
    (ψ : B →⋆ₐ[ℂ] C) (φ : A →⋆ₐ[ℂ] B) :
    (unitalMap l ψ).comp (unitalMap l φ) = unitalMap l (ψ.comp φ) := by
  ext x; simp [← NonUnitalStarAlgHom.comp_apply, map_comp, ← toNonUnital_comp]

variable (A) in
/-- Canonical surjective unital quotient `⋆`-homomorphism along a finer filter `l' ≤ l`. -/
def unitalFactor {l l' : Filter ι} (h : l' ≤ l) :
    CStarFilterQuotient A l →⋆ₐ[ℂ] CStarFilterQuotient A l' :=
  TwoSidedIdeal.Quotient.liftUnitalStarAlgHom (lp.nullIdeal (fun _ : ι ↦ A) l)
    (unitalMk A l') fun _ ha ↦ by
      rw [unitalMk_apply, mk_apply, TwoSidedIdeal.Quotient.eq_zero_iff_mem]
      exact lp.nullIdeal_antitone h ha

@[simp low]
theorem unitalFactor_apply {l l' : Filter ι} (h : l' ≤ l) (x : CStarFilterQuotient A l) :
    unitalFactor A h x = factor A h x := by
  obtain ⟨a, rfl⟩ := mk_surjective l x
  rw [factor_mk, mk_apply, unitalFactor, TwoSidedIdeal.Quotient.liftUnitalStarAlgHom_mk,
    unitalMk_apply]

@[simp]
theorem toNonUnitalStarAlgHom_unitalFactor {l l' : Filter ι} (h : l' ≤ l) :
    (unitalFactor A h).toNonUnitalStarAlgHom = factor A h :=
  NonUnitalStarAlgHom.ext fun x ↦
    (congrFun (StarAlgHom.coe_toNonUnitalStarAlgHom (unitalFactor A h)) x).trans
      (unitalFactor_apply h x)

/-- Passing to a finer filter `l' ≤ l` gives a surjective unital quotient map on
`CStarFilterQuotient`. -/
theorem unitalFactor_surjective {l l' : Filter ι} (h : l' ≤ l) :
    Function.Surjective (unitalFactor A h) := fun x ↦ by
  obtain ⟨y, rfl⟩ := factor_surjective (A := A) h x; exact ⟨y, unitalFactor_apply h y⟩

@[simp]
theorem unitalFactor_comp_unitalDiag {l l' : Filter ι} (h : l' ≤ l) :
    (unitalFactor A h).comp (unitalDiag A l) = unitalDiag A l' := by ext; simp

@[simp]
theorem unitalFactor_refl (l : Filter ι) :
    unitalFactor A (le_refl l) = StarAlgHom.id ℂ (CStarFilterQuotient A l) := by ext; simp

theorem unitalFactor_trans {l₁ l₂ l₃ : Filter ι} (h₂₃ : l₃ ≤ l₂) (h₁₂ : l₂ ≤ l₁) :
    (unitalFactor A h₂₃).comp (unitalFactor A h₁₂) = unitalFactor A (h₂₃.trans h₁₂) := by
  ext x; simp [← NonUnitalStarAlgHom.comp_apply, factor_trans]

variable (A) in
/-- Unital reindexing `a ↦ a ∘ r` along `Tendsto r l' l`. -/
def unitalReindex {l : Filter ι} {l' : Filter ι'} {r : ι' → ι} (hr : Tendsto r l' l) :
    CStarFilterQuotient A l →⋆ₐ[ℂ] CStarFilterQuotient A l' :=
  TwoSidedIdeal.Quotient.liftUnitalStarAlgHom (lp.nullIdeal (fun _ : ι ↦ A) l)
    ((unitalMk A l').comp (lp.reindexStarAlgHom ℂ A r)) fun a ha ↦ by
      rw [StarAlgHom.comp_apply, unitalMk_apply, mk_eq_zero_iff]
      simpa only [Function.comp_def, lp.reindexStarAlgHom_apply] using
        (lp.mem_nullIdeal.mp ha).comp hr

@[simp]
theorem toNonUnitalStarAlgHom_unitalReindex {l : Filter ι} {l' : Filter ι'} {r : ι' → ι}
    (hr : Tendsto r l' l) : (unitalReindex A hr).toNonUnitalStarAlgHom = reindex A hr := by
  simp only [unitalReindex, reindex, toNonUnital_comp, toNonUnitalStarAlgHom_unitalMk,
    lp.toNonUnitalStarAlgHom_reindexStarAlgHom,
    TwoSidedIdeal.Quotient.toNonUnitalStarAlgHom_liftUnitalStarAlgHom]; rfl

@[simp low]
theorem unitalReindex_apply {l : Filter ι} {l' : Filter ι'} {r : ι' → ι} (hr : Tendsto r l' l)
    (x : CStarFilterQuotient A l) : unitalReindex A hr x = reindex A hr x := by
  rw [← StarAlgHom.coe_toNonUnitalStarAlgHom (unitalReindex A hr),
    toNonUnitalStarAlgHom_unitalReindex]; rfl

@[simp]
theorem unitalReindex_comp_unitalDiag {l : Filter ι} {l' : Filter ι'} {r : ι' → ι}
    (hr : Tendsto r l' l) : (unitalReindex A hr).comp (unitalDiag A l) = unitalDiag A l' := by
  ext; simp

@[simp]
theorem unitalReindex_id (l : Filter ι) :
    unitalReindex A (tendsto_id : Tendsto id l l) =
      StarAlgHom.id ℂ (CStarFilterQuotient A l) := by ext; simp

theorem unitalReindex_comp {ι'' : Type*} {l : Filter ι} {l' : Filter ι'} {l'' : Filter ι''}
    {r : ι' → ι} {s : ι'' → ι'} (hs : Tendsto s l'' l') (hr : Tendsto r l' l) :
    (unitalReindex A hs).comp (unitalReindex A hr) = unitalReindex A (hr.comp hs) := by
  ext x; simp [← NonUnitalStarAlgHom.comp_apply, reindex_comp]

/-- Unital `StarSubalgebra.centralizer` version of the asymptotic-commutator characterization. -/
theorem mem_starSubalgebra_centralizer_range_diag_comp_iff {F C : Type*} [Star C]
    [FunLike F C A] [StarHomClass F C A] (l : Filter ι) (φ : F) (a : lp (fun _ : ι ↦ A) ∞) :
    mk A l a ∈ StarSubalgebra.centralizer ℂ (Set.range fun c ↦ diag A l (φ c)) ↔
      ∀ c : C, Tendsto (fun i ↦ ‖φ c * a i - a i * φ c‖) l (𝓝 0) := by
  rw [← SetLike.mem_coe, StarSubalgebra.coe_centralizer, ← NonUnitalStarSubalgebra.coe_centralizer
    (R := ℂ), SetLike.mem_coe]
  exact mem_centralizer_range_diag_comp_iff l φ a

/-- Special case `φ = id` for `StarSubalgebra.centralizer`. -/
theorem mem_starSubalgebra_centralizer_range_diag_iff (l : Filter ι) (a : lp (fun _ : ι ↦ A) ∞) :
    mk A l a ∈ StarSubalgebra.centralizer ℂ (Set.range (diag A l)) ↔
      ∀ b : A, Tendsto (fun i ↦ ‖b * a i - a i * b‖) l (𝓝 0) :=
  mem_starSubalgebra_centralizer_range_diag_comp_iff l (NonUnitalStarAlgHom.id ℂ A) a

end Unital

section ParitySeparation

variable (A : Type*) [CStarAlgebra A]

/-- The parity indicator sequence `n ↦ if Even n then 1 else 0` in `ℓ^∞(ℕ, A)`, which separates
`CStarSequenceAlgebra A` from `CStarUltrapower A ω`. -/
def evenIndicatorOne : lp (fun _ : ℕ ↦ A) ∞ := by
  classical
  exact ⟨fun n ↦ if Even n then 1 else 0, memℓp_infty ⟨1, by
    rintro _ ⟨n, rfl⟩
    by_cases hn : Even n <;> simp [hn, IsStarProjection.norm_le (1 : A) (.one A)]⟩⟩

theorem evenIndicatorOne_apply (n : ℕ) [Decidable (Even n)] :
    evenIndicatorOne A n = if Even n then 1 else 0 := by classical simp [evenIndicatorOne]

/-- The parity indicator sequence `evenIndicatorOne A` is a star projection in `ℓ^∞(ℕ, A)`. -/
theorem isStarProjection_evenIndicatorOne : IsStarProjection (evenIndicatorOne A) := by
  classical
  refine lp.isStarProjection_iff.mpr fun n ↦ ?_
  rw [evenIndicatorOne_apply]; split_ifs <;> simp [IsStarProjection.one, IsStarProjection.zero]

variable [Nontrivial A]

/-- In `CStarSequenceAlgebra A`, the parity indicator sequence `(1, 0, 1, 0, …)` has norm `1`. -/
@[simp]
theorem norm_mk_atTop_evenIndicatorOne : ‖mk A atTop (evenIndicatorOne A)‖ = 1 := by
  refine le_antisymm (IsStarProjection.norm_le _
    ((isStarProjection_evenIndicatorOne A).map (mk A atTop))) ?_
  rw [norm_mk]
  refine le_limsup_of_frequently_le ?_
    (isBoundedUnder_of ⟨‖evenIndicatorOne A‖,
      fun n ↦ lp.norm_apply_le_norm ENNReal.top_ne_zero _ n⟩)
  rw [frequently_atTop]; intro N; classical
  exact ⟨2 * N, by omega, by simp [evenIndicatorOne_apply]⟩

/-- In `CStarUltrapower A ω`, the parity indicator sequence equals `1` if `{n | Even n} ∈ ω`. -/
theorem mk_ultrafilter_evenIndicatorOne_of_mem {ω : Ultrafilter ℕ} (hω : {n | Even n} ∈ ω) :
    mk A (ω : Filter ℕ) (evenIndicatorOne A) = 1 := by
  rw [← mk_one (A := A) (ω : Filter ℕ), mk_eq_mk_iff]
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [hω] with n hn; classical simp [evenIndicatorOne_apply, show Even n from hn]

/-- In `CStarUltrapower A ω`, the parity indicator sequence equals `0` if `{n | Even n} ∉ ω`. -/
theorem mk_ultrafilter_evenIndicatorOne_of_notMem {ω : Ultrafilter ℕ} (hω : {n | Even n} ∉ ω) :
    mk A (ω : Filter ℕ) (evenIndicatorOne A) = 0 := by
  rw [mk_eq_zero_iff]
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [Ultrafilter.compl_mem_iff_notMem.mpr hω] with n hn
  classical simp [evenIndicatorOne_apply, show ¬ Even n from hn]

end ParitySeparation

end CStarFilterQuotient

namespace CStarSequenceAlgebra

variable {A : Type*} [NonUnitalCStarAlgebra A]

variable (A) in
/-- Isometric `⋆`-isomorphism identifying `CStarSequenceAlgebra A` (`atTop`) with the quotient by
`lp.c0Ideal` (`cofinite` on `ℕ`). -/
def equivQuotientC0Ideal :
    CStarSequenceAlgebra A ≃⋆ₐ[ℂ] lp (fun _ : ℕ ↦ A) ∞ ⧸ lp.c0Ideal (fun _ : ℕ ↦ A) :=
  TwoSidedIdeal.Quotient.quotStarAlgEquivOfEq <| by rw [← Nat.cofinite_eq_atTop]

@[simp]
theorem equivQuotientC0Ideal_mk (a : lp (fun _ : ℕ ↦ A) ∞) :
    equivQuotientC0Ideal A (CStarFilterQuotient.mk A atTop a) =
      TwoSidedIdeal.Quotient.mk (lp.c0Ideal (fun _ : ℕ ↦ A)) a := by
  rw [CStarFilterQuotient.mk_apply]; exact TwoSidedIdeal.Quotient.quotStarAlgEquivOfEq_mk _ a

@[simp]
theorem equivQuotientC0Ideal_symm_mk (a : lp (fun _ : ℕ ↦ A) ∞) :
    (equivQuotientC0Ideal A).symm (TwoSidedIdeal.Quotient.mk (lp.c0Ideal (fun _ : ℕ ↦ A)) a) =
      CStarFilterQuotient.mk A atTop a := by
  rw [equivQuotientC0Ideal, TwoSidedIdeal.Quotient.quotStarAlgEquivOfEq_symm,
    TwoSidedIdeal.Quotient.quotStarAlgEquivOfEq_mk, CStarFilterQuotient.mk_apply]

/-- The harmonic sequence `n ↦ ((n + 1)⁻¹ : ℝ) • a` in `ℓ^∞(ℕ, A)`. -/
def invSuccSmul (a : A) : lp (fun _ : ℕ ↦ A) ∞ :=
  ⟨fun n ↦ ((n + 1 : ℝ)⁻¹ : ℝ) • a, memℓp_infty ⟨‖a‖, by
    rintro _ ⟨n, rfl⟩
    have hn : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    calc ‖((n + 1 : ℝ)⁻¹ : ℝ) • a‖ = (n + 1 : ℝ)⁻¹ * ‖a‖ := by
          rw [norm_smul, Real.norm_of_nonneg (by positivity)]
      _ ≤ 1 * ‖a‖ := mul_le_mul_of_nonneg_right (inv_le_one_of_one_le₀ hn) (norm_nonneg a)
      _ = ‖a‖ := one_mul _⟩⟩

@[simp]
theorem invSuccSmul_apply (a : A) (n : ℕ) : invSuccSmul a n = ((n + 1 : ℝ)⁻¹ : ℝ) • a := (rfl)

/-- The sequence `n ↦ (n + 1)⁻¹ • a` vanishes in `CStarFilterQuotient A l` for every filter
`l ≤ atTop` (in particular in both `CStarSequenceAlgebra A` and `CStarUltrapower A ω` for any free
ultrafilter `ω` on `ℕ`). -/
theorem mk_invSuccSmul_eq_zero {l : Filter ℕ} (hl : l ≤ atTop) (a : A) :
    CStarFilterQuotient.mk A l (invSuccSmul a) = 0 := by
  rw [CStarFilterQuotient.mk_eq_zero_iff]
  have h0 : Tendsto (fun n : ℕ ↦ (1 / ((n : ℝ) + 1)) * ‖a‖) atTop (𝓝 0) := by
    simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).mul_const ‖a‖
  refine (h0.congr fun n ↦ ?_).mono_left hl
  rw [invSuccSmul_apply, norm_smul, Real.norm_of_nonneg (by positivity), one_div]

end CStarSequenceAlgebra

namespace CStarUltrapower

variable {ι : Type*} {A : Type*} [NonUnitalCStarAlgebra A]

/-- **Ultralimit norm convergence.** Along an ultrafilter `ω`, the coordinate norms `‖a i‖`
converge to `‖mk A ω a‖`. -/
theorem tendsto_norm_mk (ω : Ultrafilter ι) (a : lp (fun _ : ι ↦ A) ∞) :
    Tendsto (fun i ↦ ‖a i‖) ω (𝓝 ‖CStarFilterQuotient.mk A (ω : Filter ι) a‖) := by
  rw [CStarFilterQuotient.mk_apply]; exact lp.tendsto_norm_mk_nullIdeal ω a

/-- **Ultralimit norm formula.** In `CStarUltrapower A ω`, `‖mk A ω a‖ = lim_ω ‖a i‖`. -/
theorem norm_mk_eq_limUnder (ω : Ultrafilter ι) (a : lp (fun _ : ι ↦ A) ∞) :
    ‖CStarFilterQuotient.mk A (ω : Filter ι) a‖ = limUnder (ω : Filter ι) (fun i ↦ ‖a i‖) := by
  rw [CStarFilterQuotient.mk_apply]; exact lp.norm_mk_nullIdeal_ultrafilter ω a

end CStarUltrapower

end

end TauCeti
