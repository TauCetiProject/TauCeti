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
public import TauCeti.Order.Filter.Ultrafilter
public import TauCeti.Topology.Algebra.Star.Centralizer

/-!
# Norm sequence algebras and C⋆-ultrapowers

For any (possibly non-unital) C⋆-algebra `A` and any filter `l : Filter ι`, the filter-null ideal
`lp.nullIdeal (fun _ : ι ↦ A) l` of `lp (fun _ : ι ↦ A) ∞` is closed (`lp.isClosed_nullIdeal`), so
the quotient

`TauCeti.CStarFilterQuotient A l := lp (fun _ : ι ↦ A) ∞ ⧸ lp.nullIdeal (fun _ : ι ↦ A) l`

is a C⋆-algebra (unital and nontrivial whenever `A` is unital and nontrivial). Two specializations
play a central role in the structure and classification of nuclear C⋆-algebras:

* `TauCeti.CStarSequenceAlgebra A := CStarFilterQuotient A (atTop : Filter ℕ)`, the **norm sequence
  algebra** `A_∞ = ℓ^∞(ℕ, A) / c₀(ℕ, A)`, with quotient norm `‖[a]‖ = limsup_{n → ∞} ‖a n‖`;
* `TauCeti.CStarUltrapower A ω := CStarFilterQuotient A (ω : Filter ι)` for `ω : Ultrafilter ι`, the
  **norm C⋆-ultrapower** `A_ω = ℓ^∞(ι, A) / c_ω(ι, A)`, with ultralimit norm `‖[a]‖ = lim_ω ‖a i‖`.

We establish norm-attaining bounded representatives, isometric diagonal embeddings, functoriality
under `⋆`-homomorphisms and `⋆`-equivalences, quotient maps between comparable filters, diagonal
reindexing along `Tendsto r l' l`, and the asymptotic-commutator characterization of relative
commutants (covering both `A_ω ∩ A′` and `M(A)_ω ∩ A′`). Finally, we record the separation between
`A_∞` and `A_ω` witnessed by the parity indicator sequence `(1, 0, 1, 0, …)`.

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
    Type _ :=
  lp (fun _ : ι ↦ A) ∞ ⧸ lp.nullIdeal (fun _ : ι ↦ A) l

/-- The norm sequence algebra `A_∞ = ℓ^∞(ℕ, A) / c₀(ℕ, A)` of a C⋆-algebra `A`. -/
abbrev CStarSequenceAlgebra (A : Type*) [NonUnitalNormedRing A] : Type _ :=
  CStarFilterQuotient A (atTop : Filter ℕ)

/-- The norm C⋆-ultrapower `A_ω = ℓ^∞(ι, A) / c_ω(ι, A)` of a C⋆-algebra `A` along an ultrafilter
`ω : Ultrafilter ι`. -/
abbrev CStarUltrapower (A : Type*) [NonUnitalNormedRing A] {ι : Type*} (ω : Ultrafilter ι) :
    Type _ :=
  CStarFilterQuotient A (ω : Filter ι)

namespace CStarFilterQuotient

section NonUnital

variable {ι ι' : Type*} {A B C : Type*} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
  [NonUnitalCStarAlgebra C]

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
  rw [← sub_eq_zero, ← map_sub, mk_eq_zero_iff]
  simp only [lp.coeFn_sub, Pi.sub_apply]

/-- **Quotient norm formula.** For any nontrivial filter `l`, `‖mk A l a‖ = limsup_i ‖a i‖` along
`l`. -/
theorem norm_mk {l : Filter ι} [l.NeBot] (a : lp (fun _ : ι ↦ A) ∞) :
    ‖mk A l a‖ = limsup (fun i ↦ ‖a i‖) l := by
  rw [mk_apply]
  exact lp.norm_mk_nullIdeal a

theorem norm_mk_le (l : Filter ι) (a : lp (fun _ : ι ↦ A) ∞) : ‖mk A l a‖ ≤ ‖a‖ := by
  rw [mk_apply]
  exact TwoSidedIdeal.Quotient.norm_mk_le _ a

/-- **Bounded norm-attaining representative.** Every element `x : CStarFilterQuotient A l` lifts to
a bounded family `a : lp (fun _ : ι ↦ A) ∞` with `‖a‖ = ‖x‖`. -/
theorem exists_mk_eq_and_norm_eq (l : Filter ι) (x : CStarFilterQuotient A l) :
    ∃ a : lp (fun _ : ι ↦ A) ∞, mk A l a = x ∧ ‖a‖ = ‖x‖ := by
  simpa only [mk_apply] using lp.exists_mk_nullIdeal_eq_and_norm_eq l x

variable (A) in
/-- The diagonal embedding `A →⋆ₙₐ[ℂ] CStarFilterQuotient A l` sending `a` to the class of the
constant family `fun _ ↦ a`. -/
def diag (l : Filter ι) : A →⋆ₙₐ[ℂ] CStarFilterQuotient A l :=
  (mk A l).comp (lp.constStarAlgHom ℂ ι A)

theorem diag_eq_mk_const (l : Filter ι) (a : A) :
    diag A l a = mk A l (lp.constStarAlgHom ℂ ι A a) :=
  (rfl)

@[simp]
theorem norm_diag {l : Filter ι} [l.NeBot] (a : A) : ‖diag A l a‖ = ‖a‖ := by
  rw [diag_eq_mk_const, norm_mk]
  simp

/-- The diagonal embedding `diag A l` is an isometry whenever `l` is nontrivial. -/
theorem isometry_diag (l : Filter ι) [l.NeBot] : Isometry (diag A l) :=
  AddMonoidHomClass.isometry_of_norm _ norm_diag

/-- The diagonal embedding `diag A l` is injective whenever `l` is nontrivial. -/
theorem diag_injective (l : Filter ι) [l.NeBot] : Function.Injective (diag A l) :=
  (isometry_diag l).injective

/-- `CStarFilterQuotient A l` is nontrivial whenever `A` and `l` are nontrivial. -/
instance nontrivial [Nontrivial A] {l : Filter ι} [l.NeBot] :
    Nontrivial (CStarFilterQuotient A l) :=
  (diag_injective (A := A) l).nontrivial

/-- Functoriality of `CStarFilterQuotient` along a non-unital `⋆`-homomorphism `φ : A →⋆ₙₐ[ℂ] B`. -/
def map (l : Filter ι) (φ : A →⋆ₙₐ[ℂ] B) :
    CStarFilterQuotient A l →⋆ₙₐ[ℂ] CStarFilterQuotient B l :=
  TwoSidedIdeal.Quotient.liftStarAlgHom (lp.nullIdeal (fun _ : ι ↦ A) l)
    ((mk B l).comp (lp.mapStarAlgHom fun _ ↦ φ)) fun a ha ↦ by
      rw [NonUnitalStarAlgHom.comp_apply, mk_eq_zero_iff]
      exact squeeze_zero (fun _ ↦ norm_nonneg _)
        (fun i ↦ by
          rw [lp.mapStarAlgHom_apply]
          exact NonUnitalStarAlgHom.norm_apply_le φ (a i))
        (lp.mem_nullIdeal.1 ha)

@[simp]
theorem map_mk (l : Filter ι) (φ : A →⋆ₙₐ[ℂ] B) (a : lp (fun _ : ι ↦ A) ∞) :
    map l φ (mk A l a) = mk B l (lp.mapStarAlgHom (fun _ ↦ φ) a) := by
  rw [mk_apply]
  exact TwoSidedIdeal.Quotient.liftStarAlgHom_mk _ _ _ a

@[simp]
theorem map_comp_diag (l : Filter ι) (φ : A →⋆ₙₐ[ℂ] B) :
    (map l φ).comp (diag A l) = (diag B l).comp φ := by
  ext a
  simp only [NonUnitalStarAlgHom.comp_apply, diag_eq_mk_const, map_mk]
  congr 1
  ext i
  simp

@[simp]
theorem map_diag (l : Filter ι) (φ : A →⋆ₙₐ[ℂ] B) (a : A) :
    map l φ (diag A l a) = diag B l (φ a) :=
  DFunLike.congr_fun (map_comp_diag l φ) a

@[simp]
theorem map_id (l : Filter ι) :
    map l (NonUnitalStarAlgHom.id ℂ A) = NonUnitalStarAlgHom.id ℂ (CStarFilterQuotient A l) := by
  refine NonUnitalStarAlgHom.ext fun x ↦ ?_
  obtain ⟨a, rfl⟩ := mk_surjective l x
  simp

theorem map_comp (l : Filter ι) (ψ : B →⋆ₙₐ[ℂ] C) (φ : A →⋆ₙₐ[ℂ] B) :
    (map l ψ).comp (map l φ) = map l (ψ.comp φ) := by
  refine NonUnitalStarAlgHom.ext fun x ↦ ?_
  obtain ⟨a, rfl⟩ := mk_surjective l x
  simp only [NonUnitalStarAlgHom.comp_apply, map_mk]
  congr 1
  ext i
  simp

/-- An injective `⋆`-homomorphism induces an injective map on `CStarFilterQuotient`. -/
theorem map_injective_of_injective (l : Filter ι) {φ : A →⋆ₙₐ[ℂ] B}
    (hφ : Function.Injective φ) : Function.Injective (map l φ) := by
  refine TwoSidedIdeal.Quotient.liftStarAlgHom_injective_of_ker_le _ fun a ha ↦ ?_
  rw [TwoSidedIdeal.mem_ker, NonUnitalStarAlgHom.comp_apply, mk_eq_zero_iff] at ha
  exact lp.mem_nullIdeal.2 (by simpa [NonUnitalStarAlgHom.norm_map φ hφ] using ha)

/-- An injective `⋆`-homomorphism induces an isometric map on `CStarFilterQuotient`. -/
theorem isometry_map (l : Filter ι) {φ : A →⋆ₙₐ[ℂ] B} (hφ : Function.Injective φ) :
    Isometry (map l φ) :=
  NonUnitalStarAlgHom.isometry _ (map_injective_of_injective l hφ)

/-- Functorial `⋆`-isomorphism on `CStarFilterQuotient` induced by `e : A ≃⋆ₐ[ℂ] B`. -/
def mapEquiv (l : Filter ι) (e : A ≃⋆ₐ[ℂ] B) :
    CStarFilterQuotient A l ≃⋆ₐ[ℂ] CStarFilterQuotient B l :=
  StarAlgEquiv.ofNonUnitalStarAlgHom (map l e.toNonUnitalStarAlgHom)
    (map l e.symm.toNonUnitalStarAlgHom)
    (by
      rw [map_comp]
      convert map_id (A := A) l
      ext a
      exact e.symm_apply_apply a)
    (by
      rw [map_comp]
      convert map_id (A := B) l
      ext b
      exact e.apply_symm_apply b)

@[simp]
theorem mapEquiv_mk (l : Filter ι) (e : A ≃⋆ₐ[ℂ] B) (a : lp (fun _ : ι ↦ A) ∞) :
    mapEquiv l e (mk A l a) = mk B l (lp.mapStarAlgHom (fun _ ↦ e.toNonUnitalStarAlgHom) a) :=
  map_mk l e.toNonUnitalStarAlgHom a

@[simp]
theorem mapEquiv_symm (l : Filter ι) (e : A ≃⋆ₐ[ℂ] B) :
    (mapEquiv l e).symm = mapEquiv l e.symm :=
  (rfl)

variable (A) in
/-- Canonical surjective quotient `⋆`-homomorphism when passing to a finer filter `l' ≤ l`
(for example from `CStarSequenceAlgebra A` to `CStarUltrapower A ω` for a free ultrafilter `ω`). -/
def factor {l l' : Filter ι} (h : l' ≤ l) :
    CStarFilterQuotient A l →⋆ₙₐ[ℂ] CStarFilterQuotient A l' :=
  TwoSidedIdeal.Quotient.factorStarAlgHom (lp.nullIdeal_antitone (A := fun _ : ι ↦ A) h)

@[simp]
theorem factor_mk {l l' : Filter ι} (h : l' ≤ l) (a : lp (fun _ : ι ↦ A) ∞) :
    factor A h (mk A l a) = mk A l' a := by
  rw [mk_apply, mk_apply, factor]
  exact TwoSidedIdeal.Quotient.factorStarAlgHom_mk
    (lp.nullIdeal_antitone (A := fun _ : ι ↦ A) h) a

/-- Passing to a finer filter `l' ≤ l` gives a surjective quotient map on `CStarFilterQuotient`. -/
theorem factor_surjective {l l' : Filter ι} (h : l' ≤ l) :
    Function.Surjective (factor A h) := by
  rw [factor]
  exact TwoSidedIdeal.Quotient.factorStarAlgHom_surjective
    (lp.nullIdeal_antitone (A := fun _ : ι ↦ A) h)

@[simp]
theorem factor_comp_diag {l l' : Filter ι} (h : l' ≤ l) :
    (factor A h).comp (diag A l) = diag A l' := by
  refine NonUnitalStarAlgHom.ext fun a ↦ ?_
  simp [diag_eq_mk_const]

variable (A) in
/-- Reindexing `a ↦ a ∘ r` descends to `CStarFilterQuotient A l →⋆ₙₐ[ℂ] CStarFilterQuotient A l'`
whenever `Tendsto r l' l`, and fixes the diagonal subalgebra. -/
def reindex {l : Filter ι} {l' : Filter ι'} {r : ι' → ι} (hr : Tendsto r l' l) :
    CStarFilterQuotient A l →⋆ₙₐ[ℂ] CStarFilterQuotient A l' :=
  TwoSidedIdeal.Quotient.liftStarAlgHom (lp.nullIdeal (fun _ : ι ↦ A) l)
    ((mk A l').comp (lp.reindexStarAlgHom ℂ A r)) fun a ha ↦ by
      rw [NonUnitalStarAlgHom.comp_apply, mk_eq_zero_iff]
      simpa only [Function.comp_def, lp.reindexStarAlgHom_apply] using
        (lp.mem_nullIdeal.1 ha).comp hr

@[simp]
theorem reindex_mk {l : Filter ι} {l' : Filter ι'} {r : ι' → ι} (hr : Tendsto r l' l)
    (a : lp (fun _ : ι ↦ A) ∞) :
    reindex A hr (mk A l a) = mk A l' (lp.reindexStarAlgHom ℂ A r a) := by
  rw [mk_apply]
  exact TwoSidedIdeal.Quotient.liftStarAlgHom_mk _ _ _ a

@[simp]
theorem reindex_comp_diag {l : Filter ι} {l' : Filter ι'} {r : ι' → ι} (hr : Tendsto r l' l) :
    (reindex A hr).comp (diag A l) = diag A l' := by
  refine NonUnitalStarAlgHom.ext fun a ↦ ?_
  simp only [NonUnitalStarAlgHom.comp_apply, diag_eq_mk_const, reindex_mk]
  congr 1
  ext j
  simp

@[simp]
theorem reindex_diag {l : Filter ι} {l' : Filter ι'} {r : ι' → ι} (hr : Tendsto r l' l) (a : A) :
    reindex A hr (diag A l a) = diag A l' a :=
  DFunLike.congr_fun (reindex_comp_diag (A := A) hr) a

/-- **Asymptotic-commutator characterization of relative commutants.** Given `φ : C →⋆ₙₐ[ℂ] A`, the
class `mk A l a` belongs to the relative commutant of `diag A l ∘ φ` in `CStarFilterQuotient A l` if
and only if `‖φ c * a i - a i * φ c‖ → 0` along `l` for every `c : C`. -/
theorem mem_centralizer_range_diag_comp_iff (l : Filter ι) (φ : C →⋆ₙₐ[ℂ] A)
    (a : lp (fun _ : ι ↦ A) ∞) :
    mk A l a ∈ NonUnitalStarSubalgebra.centralizer ℂ (Set.range fun c ↦ diag A l (φ c)) ↔
      ∀ c : C, Tendsto (fun i ↦ ‖φ c * a i - a i * φ c‖) l (𝓝 0) := by
  rw [NonUnitalStarSubalgebra.mem_centralizer_iff]
  constructor
  · intro h c
    have hc := (h (diag A l (φ c)) ⟨c, rfl⟩).1
    rw [diag_eq_mk_const, ← map_mul, ← map_mul, mk_eq_mk_iff] at hc
    simpa only [lp.infty_coeFn_mul, Pi.mul_apply, lp.constStarAlgHom_apply] using hc
  · rintro h _ ⟨c, rfl⟩
    dsimp only
    refine ⟨?_, ?_⟩
    · rw [diag_eq_mk_const, ← map_mul, ← map_mul, mk_eq_mk_iff]
      simpa only [lp.infty_coeFn_mul, Pi.mul_apply, lp.constStarAlgHom_apply] using h c
    · rw [← map_star, ← map_star, diag_eq_mk_const, ← map_mul, ← map_mul, mk_eq_mk_iff]
      simpa only [lp.infty_coeFn_mul, Pi.mul_apply, lp.constStarAlgHom_apply] using h (star c)

/-- Special case `φ = id`: `mk A l a` belongs to the central sequence algebra
`CStarFilterQuotient A l ∩ A′` if and only if `‖b * a i - a i * b‖ → 0` along `l` for every
`b : A`. -/
theorem mem_centralizer_range_diag_iff (l : Filter ι) (a : lp (fun _ : ι ↦ A) ∞) :
    mk A l a ∈ NonUnitalStarSubalgebra.centralizer ℂ (Set.range (diag A l)) ↔
      ∀ b : A, Tendsto (fun i ↦ ‖b * a i - a i * b‖) l (𝓝 0) :=
  mem_centralizer_range_diag_comp_iff l (NonUnitalStarAlgHom.id ℂ A) a

end NonUnital

section Unital

variable {ι ι' : Type*} {A B C : Type*} [CStarAlgebra A] [Nontrivial A]
  [CStarAlgebra B] [Nontrivial B] [NonUnitalCStarAlgebra C]

variable (A) in
/-- The canonical unital quotient `⋆`-homomorphism `ℓ^∞(ι, A) →⋆ₐ[ℂ] CStarFilterQuotient A l`. -/
def unitalMk (l : Filter ι) : lp (fun _ : ι ↦ A) ∞ →⋆ₐ[ℂ] CStarFilterQuotient A l :=
  TwoSidedIdeal.Quotient.mkUnitalStarAlgHom (lp.nullIdeal (fun _ : ι ↦ A) l)

@[simp]
theorem toNonUnitalStarAlgHom_unitalMk (l : Filter ι) :
    (unitalMk A l).toNonUnitalStarAlgHom = mk A l :=
  TwoSidedIdeal.Quotient.toNonUnitalStarAlgHom_mkUnitalStarAlgHom _

@[simp]
theorem unitalMk_apply (l : Filter ι) (a : lp (fun _ : ι ↦ A) ∞) :
    unitalMk A l a = mk A l a := by
  rw [unitalMk, TwoSidedIdeal.Quotient.mkUnitalStarAlgHom_apply, mk_apply]

theorem unitalMk_surjective (l : Filter ι) : Function.Surjective (unitalMk A l) :=
  TwoSidedIdeal.Quotient.mkUnitalStarAlgHom_surjective _

variable (A) in
/-- The unital diagonal embedding `A →⋆ₐ[ℂ] CStarFilterQuotient A l`. -/
def unitalDiag (l : Filter ι) : A →⋆ₐ[ℂ] CStarFilterQuotient A l :=
  (unitalMk A l).comp (lp.unitalConstStarAlgHom ℂ ι A)

@[simp]
theorem toNonUnitalStarAlgHom_unitalDiag (l : Filter ι) :
    (unitalDiag A l).toNonUnitalStarAlgHom = diag A l :=
  NonUnitalStarAlgHom.ext fun a ↦
    (unitalMk_apply l (lp.unitalConstStarAlgHom ℂ ι A a)).trans <|
      (congrArg (mk A l) (lp.ext <| funext fun i ↦ by simp)).trans (diag_eq_mk_const l a).symm

@[simp]
theorem unitalDiag_apply (l : Filter ι) (a : A) : unitalDiag A l a = diag A l a :=
  congrFun (congrArg (fun f : A →⋆ₙₐ[ℂ] CStarFilterQuotient A l ↦ (f : A → _))
    (toNonUnitalStarAlgHom_unitalDiag l)) a

/-- Unital functoriality of `CStarFilterQuotient` along `φ : A →⋆ₐ[ℂ] B`. -/
def unitalMap (l : Filter ι) (φ : A →⋆ₐ[ℂ] B) :
    CStarFilterQuotient A l →⋆ₐ[ℂ] CStarFilterQuotient B l :=
  TwoSidedIdeal.Quotient.liftUnitalStarAlgHom (lp.nullIdeal (fun _ : ι ↦ A) l)
    ((unitalMk B l).comp (lp.unitalMapStarAlgHom fun _ ↦ φ)) fun a ha ↦ by
      rw [StarAlgHom.comp_apply, unitalMk_apply, mk_eq_zero_iff]
      exact squeeze_zero (fun _ ↦ norm_nonneg _)
        (fun i ↦ by
          rw [lp.unitalMapStarAlgHom_apply]
          exact NonUnitalStarAlgHom.norm_apply_le φ (a i))
        (lp.mem_nullIdeal.1 ha)

@[simp]
theorem unitalMap_mk (l : Filter ι) (φ : A →⋆ₐ[ℂ] B) (a : lp (fun _ : ι ↦ A) ∞) :
    unitalMap l φ (mk A l a) = mk B l (lp.unitalMapStarAlgHom (fun _ ↦ φ) a) := by
  rw [mk_apply]
  exact (TwoSidedIdeal.Quotient.liftUnitalStarAlgHom_mk _ _ _ a).trans (unitalMk_apply l _)

@[simp]
theorem toNonUnitalStarAlgHom_unitalMap (l : Filter ι) (φ : A →⋆ₐ[ℂ] B) :
    (unitalMap l φ).toNonUnitalStarAlgHom = map l φ.toNonUnitalStarAlgHom := by
  refine NonUnitalStarAlgHom.ext fun x ↦ ?_
  obtain ⟨a, rfl⟩ := mk_surjective l x
  exact (unitalMap_mk l φ a).trans <|
    (congrArg (mk B l) (lp.ext <| funext fun _ ↦ by simp)).trans
      (map_mk l φ.toNonUnitalStarAlgHom a).symm

variable (A) in
/-- Unital reindexing `a ↦ a ∘ r` along `Tendsto r l' l`. -/
def unitalReindex {l : Filter ι} {l' : Filter ι'} {r : ι' → ι} (hr : Tendsto r l' l) :
    CStarFilterQuotient A l →⋆ₐ[ℂ] CStarFilterQuotient A l' :=
  TwoSidedIdeal.Quotient.liftUnitalStarAlgHom (lp.nullIdeal (fun _ : ι ↦ A) l)
    ((unitalMk A l').comp (lp.unitalReindexStarAlgHom ℂ A r)) fun a ha ↦ by
      rw [StarAlgHom.comp_apply, unitalMk_apply, mk_eq_zero_iff]
      simpa only [Function.comp_def, lp.unitalReindexStarAlgHom_apply] using
        (lp.mem_nullIdeal.1 ha).comp hr

@[simp]
theorem unitalReindex_mk {l : Filter ι} {l' : Filter ι'} {r : ι' → ι} (hr : Tendsto r l' l)
    (a : lp (fun _ : ι ↦ A) ∞) :
    unitalReindex A hr (mk A l a) = mk A l' (lp.unitalReindexStarAlgHom ℂ A r a) := by
  rw [mk_apply]
  exact (TwoSidedIdeal.Quotient.liftUnitalStarAlgHom_mk _ _ _ a).trans (unitalMk_apply l' _)

@[simp]
theorem toNonUnitalStarAlgHom_unitalReindex {l : Filter ι} {l' : Filter ι'} {r : ι' → ι}
    (hr : Tendsto r l' l) :
    (unitalReindex A hr).toNonUnitalStarAlgHom = reindex A hr := by
  refine NonUnitalStarAlgHom.ext fun x ↦ ?_
  obtain ⟨a, rfl⟩ := mk_surjective l x
  exact (unitalReindex_mk hr a).trans <|
    (congrArg (mk A l') (lp.ext <| funext fun _ ↦ by simp)).trans (reindex_mk hr a).symm

@[simp]
theorem unitalReindex_comp_unitalDiag {l : Filter ι} {l' : Filter ι'} {r : ι' → ι}
    (hr : Tendsto r l' l) :
    (unitalReindex A hr).comp (unitalDiag A l) = unitalDiag A l' := by
  ext a
  exact (congrArg (unitalReindex A hr) (unitalDiag_apply l a)).trans <|
    (congrFun (congrArg (fun f : _ →⋆ₙₐ[ℂ] _ ↦ (f : _ → _))
      (toNonUnitalStarAlgHom_unitalReindex (A := A) hr)) (diag A l a)).trans
        ((reindex_diag hr a).trans (unitalDiag_apply l' a).symm)

/-- Unital `StarSubalgebra.centralizer` version of the asymptotic-commutator characterization. -/
theorem mem_starSubalgebra_centralizer_range_diag_comp_iff (l : Filter ι) (φ : C →⋆ₙₐ[ℂ] A)
    (a : lp (fun _ : ι ↦ A) ∞) :
    mk A l a ∈ StarSubalgebra.centralizer ℂ (Set.range fun c ↦ diag A l (φ c)) ↔
      ∀ c : C, Tendsto (fun i ↦ ‖φ c * a i - a i * φ c‖) l (𝓝 0) := by
  rw [← SetLike.mem_coe, StarSubalgebra.coe_centralizer, ← NonUnitalStarSubalgebra.coe_centralizer
    (R := ℂ), SetLike.mem_coe]
  exact mem_centralizer_range_diag_comp_iff l φ a

end Unital

end CStarFilterQuotient

namespace CStarSequenceAlgebra

variable {A : Type*} [NonUnitalCStarAlgebra A]

variable (A) in
/-- Isometric `⋆`-isomorphism identifying `CStarSequenceAlgebra A` (`atTop`) with the quotient by
`lp.c0Ideal` (`cofinite` on `ℕ`). -/
def equivQuotientC0Ideal :
    CStarSequenceAlgebra A ≃⋆ₐ[ℂ] lp (fun _ : ℕ ↦ A) ∞ ⧸ lp.c0Ideal (fun _ : ℕ ↦ A) :=
  TwoSidedIdeal.Quotient.quotStarAlgEquivOfEq <| by
    rw [lp.c0Ideal_eq_nullIdeal, Nat.cofinite_eq_atTop]

@[simp]
theorem equivQuotientC0Ideal_mk (a : lp (fun _ : ℕ ↦ A) ∞) :
    equivQuotientC0Ideal A (CStarFilterQuotient.mk A atTop a) =
      TwoSidedIdeal.Quotient.mk (lp.c0Ideal (fun _ : ℕ ↦ A)) a := by
  rw [CStarFilterQuotient.mk_apply]
  exact TwoSidedIdeal.Quotient.quotStarAlgEquivOfEq_mk _ a

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
theorem invSuccSmul_apply (a : A) (n : ℕ) :
    invSuccSmul a n = ((n + 1 : ℝ)⁻¹ : ℝ) • a :=
  (rfl)

/-- The sequence `n ↦ (n + 1)⁻¹ • a` vanishes in `CStarFilterQuotient A l` for every filter
`l ≤ atTop` (in particular in both `CStarSequenceAlgebra A` and `CStarUltrapower A ω` for any free
ultrafilter `ω` on `ℕ`). -/
theorem mk_invSuccSmul_eq_zero {l : Filter ℕ} (hl : l ≤ atTop) (a : A) :
    CStarFilterQuotient.mk A l (invSuccSmul a) = 0 := by
  rw [CStarFilterQuotient.mk_eq_zero_iff]
  have h0 : Tendsto (fun n : ℕ ↦ (1 / ((n : ℝ) + 1)) * ‖a‖) atTop (𝓝 0) := by
    simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).mul_const ‖a‖
  have ht : Tendsto (fun n : ℕ ↦ ‖invSuccSmul a n‖) atTop (𝓝 0) :=
    h0.congr fun n ↦ by
      rw [invSuccSmul_apply, norm_smul, Real.norm_of_nonneg (by positivity), one_div]
  exact ht.mono_left hl

end CStarSequenceAlgebra

namespace CStarUltrapower

variable {ι : Type*} {A : Type*} [NonUnitalCStarAlgebra A]

/-- **Ultralimit norm convergence.** Along an ultrafilter `ω`, the coordinate norms `‖a i‖`
converge to `‖mk A ω a‖`. -/
theorem tendsto_norm_mk (ω : Ultrafilter ι) (a : lp (fun _ : ι ↦ A) ∞) :
    Tendsto (fun i ↦ ‖a i‖) ω (𝓝 ‖CStarFilterQuotient.mk A (ω : Filter ι) a‖) := by
  rw [CStarFilterQuotient.mk_apply]
  exact lp.tendsto_norm_mk_nullIdeal ω a

/-- **Ultralimit norm formula.** In `CStarUltrapower A ω`, `‖mk A ω a‖ = lim_ω ‖a i‖`. -/
theorem norm_mk_eq_limUnder (ω : Ultrafilter ι) (a : lp (fun _ : ι ↦ A) ∞) :
    ‖CStarFilterQuotient.mk A (ω : Filter ι) a‖ = limUnder (ω : Filter ι) (fun i ↦ ‖a i‖) := by
  rw [CStarFilterQuotient.mk_apply]
  exact lp.norm_mk_nullIdeal_ultrafilter ω a

end CStarUltrapower

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
    evenIndicatorOne A n = if Even n then 1 else 0 := by
  classical
  simp [evenIndicatorOne]

/-- The parity indicator sequence `evenIndicatorOne A` is a star projection in `ℓ^∞(ℕ, A)`. -/
theorem isStarProjection_evenIndicatorOne : IsStarProjection (evenIndicatorOne A) := by
  classical
  rw [lp.isStarProjection_iff]
  intro n
  rw [evenIndicatorOne_apply]
  split_ifs <;> simp [IsStarProjection.one, IsStarProjection.zero]

variable [Nontrivial A]

/-- In `CStarSequenceAlgebra A`, the parity indicator sequence `(1, 0, 1, 0, …)` has norm `1`. -/
@[simp]
theorem norm_mk_atTop_evenIndicatorOne :
    ‖CStarFilterQuotient.mk A atTop (evenIndicatorOne A)‖ = 1 := by
  have hp : IsStarProjection (CStarFilterQuotient.mk A atTop (evenIndicatorOne A)) :=
    (isStarProjection_evenIndicatorOne A).map (CStarFilterQuotient.mk A atTop)
  refine le_antisymm (IsStarProjection.norm_le _ hp) ?_
  rw [CStarFilterQuotient.norm_mk]
  refine le_limsup_of_frequently_le ?_
    (isBoundedUnder_of ⟨‖evenIndicatorOne A‖,
      fun n ↦ lp.norm_apply_le_norm ENNReal.top_ne_zero _ n⟩)
  rw [frequently_atTop]
  intro N
  classical
  refine ⟨2 * N, by omega, ?_⟩
  simp [evenIndicatorOne_apply]

/-- In `CStarUltrapower A ω`, the parity indicator sequence equals `1` if `{n | Even n} ∈ ω`. -/
theorem mk_ultrafilter_evenIndicatorOne_of_mem {ω : Ultrafilter ℕ}
    (hω : {n | Even n} ∈ ω) :
    CStarFilterQuotient.mk A (ω : Filter ℕ) (evenIndicatorOne A) = 1 := by
  rw [← map_one (CStarFilterQuotient.unitalMk A (ω : Filter ℕ)),
    CStarFilterQuotient.unitalMk_apply, CStarFilterQuotient.mk_eq_mk_iff]
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [hω] with n hn
  have hn' : Even n := hn
  classical
  simp [evenIndicatorOne_apply, hn']

/-- In `CStarUltrapower A ω`, the parity indicator sequence equals `0` if `{n | Even n} ∉ ω`. -/
theorem mk_ultrafilter_evenIndicatorOne_of_notMem {ω : Ultrafilter ℕ}
    (hω : {n | Even n} ∉ ω) :
    CStarFilterQuotient.mk A (ω : Filter ℕ) (evenIndicatorOne A) = 0 := by
  rw [CStarFilterQuotient.mk_eq_zero_iff]
  have hcompl : ({n | Even n}ᶜ : Set ℕ) ∈ ω := Ultrafilter.compl_mem_iff_notMem.2 hω
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [hcompl] with n hn
  have hn' : ¬ Even n := hn
  classical
  simp [evenIndicatorOne_apply, hn']

end ParitySeparation

end

end TauCeti
