/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Equiv
public import Mathlib.Algebra.Module.Submodule.Map
public import Mathlib.Algebra.Module.Equiv.Basic
public import Mathlib.LinearAlgebra.Prod
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.RingTheory.Ideal.Maps
import Mathlib.Algebra.Ring.Int.Units
import TauCeti.LinearAlgebra.Span.Basic

/-!
# Elementary linear-equivalence transport

Transport of submodule stability through an intertwining semilinear equivalence.
Symmetry of a linear automorphism agrees with inversion in its group structure, and commutes with
restriction of scalars.
Through a linear equivalence `L : M ≃ₗ[R] M₁ × M₂`, the vectors `L⁻¹ (0, vᵢ)` for a spanning
family `v` of `M₂` span the kernel of `u ↦ (L u).1`.
A ring isomorphism over a common target carries the kernel of one map to the kernel of the other.
Composites of rescaled linear equivalences rescale by the quotient of the factors.
Linear maps conjugate under linear equivalences have linearly equivalent kernels and cokernels,
`LinearMap.kerEquivOfComp` and `LinearMap.cokerEquivOfComp`.
Coordinate relabelling of function modules (`LinearEquiv.funCongrLeft`) is injective in the
coordinate equivalence over a nontrivial target module.
Every `R`-linear automorphism of a rank-one free `R`-module `ι → R` over a commutative semiring `R`
is scalar multiplication by a unit (`LinearEquiv.exists_eq_smulOfUnit_of_unique`), specializing over
`ℤ` to `LinearMap.id` or `-LinearMap.id` (`LinearEquiv.toLinearMap_eq_id_or_neg_of_unique`).
Conjugating an algebra homomorphism into `Module.End` by `LinearEquiv.conjAlgEquiv` agrees with
pointwise intertwining (`LinearEquiv.conjAlgEquiv_toAlgHom_comp_eq_iff`).
Following the identification of equal submodules by an inclusion is the other inclusion,
`Submodule.subtype_comp_ofEq`.
-/

public section

namespace LinearEquiv

/-- Symmetry of a linear automorphism is its group inverse. -/
theorem symm_eq_inv {R V : Type*} [Semiring R] [AddCommMonoid V] [Module R V]
    (e : V ≃ₗ[R] V) : e.symm = e⁻¹ := rfl

/-- The inverse of a linear equivalence with restricted scalars is the inverse with restricted
scalars. -/
@[simp]
theorem symm_restrictScalars {R S M M₂ : Type*} [Semiring R] [Semiring S] [AddCommMonoid M]
    [AddCommMonoid M₂] [Module R M] [Module R M₂] [Module S M] [Module S M₂]
    [LinearMap.CompatibleSMul M M₂ R S] [LinearMap.CompatibleSMul M₂ M R S] (e : M ≃ₗ[S] M₂) :
    (e.restrictScalars R).symm = e.symm.restrictScalars R :=
  rfl

/-- Transport stability of a mapped submodule through an intertwining semilinear
equivalence. -/
theorem mem_of_preserves_map
    {R S V W : Type*} [Semiring R] [Semiring S]
    [AddCommMonoid V] [Module R V] [AddCommMonoid W] [Module S W]
    {σ : R →+* S} {σ' : S →+* R} [RingHomInvPair σ σ'] [RingHomInvPair σ' σ]
    (e : V ≃ₛₗ[σ] W) (p : Submodule R V) (q : Submodule S W)
    (hmap : p.map (e : V →ₛₗ[σ] W) = q) (f : V → V) (g : W → W)
    (hcomm : ∀ x, e (f x) = g (e x))
    (hstable : ∀ {y}, y ∈ q → g y ∈ q)
    {x : V} (hx : x ∈ p) : f x ∈ p := by
  subst hmap
  simpa [← hcomm] using hstable (Submodule.mem_map_of_mem hx)

/-- Through a linear equivalence `L : M ≃ₗ[R] M₁ × M₂`, the vectors `L⁻¹ (0, vᵢ)` for a spanning
family `v` of `M₂` span the kernel of the first component `u ↦ (L u).1`. -/
theorem span_range_symm_inr_eq_ker {R M M₁ M₂ ι : Type*} [Semiring R]
    [AddCommMonoid M] [Module R M] [AddCommMonoid M₁] [Module R M₁]
    [AddCommMonoid M₂] [Module R M₂] (L : M ≃ₗ[R] M₁ × M₂) {v : ι → M₂}
    (hv : Submodule.span R (Set.range v) = ⊤) :
    Submodule.span R (Set.range fun i ↦ L.symm (0, v i)) =
      LinearMap.ker (LinearMap.fst R M₁ M₂ ∘ₗ L.toLinearMap) := by
  -- The vectors are the values of `L.symm ∘ inr` on `v`, so they span its range.
  have hspan : Submodule.span R (Set.range fun i ↦ L.symm (0, v i)) =
      LinearMap.range (L.symm.toLinearMap ∘ₗ LinearMap.inr R M₁ M₂) := by
    rw [← Submodule.span_eq (LinearMap.range _), LinearMap.coe_range,
      Submodule.span_range_eq_span_range_comp_of_span_eq_top hv]
    rfl
  -- The range of `L.symm ∘ inr` is the image under `L.symm` of `{0} × M₂ = ker (fst)`.
  rw [hspan, LinearMap.range_comp, LinearMap.range_inr, LinearMap.ker_comp,
    Submodule.map_equiv_eq_comap_symm, L.symm_symm]

/-- If two isomorphisms `M₁` and `M₂` out of a common space are the multiples `c₁` and `c₂` of
isomorphisms `M₁'` and `M₂'`, with `c₂ ≠ 0`, then `M₁ ∘ M₂⁻¹` is the multiple `c₁ / c₂` of
`M₁' ∘ M₂'⁻¹`. -/
theorem apply_symm_eq_div_smul {R A B C : Type*} [Semifield R] [AddCommMonoid A] [Module R A]
    [AddCommMonoid B] [Module R B] [AddCommMonoid C] [Module R C] (M₁ M₁' : A ≃ₗ[R] B)
    (M₂ M₂' : A ≃ₗ[R] C) {c₁ c₂ : R} (h₁ : ∀ a, M₁ a = c₁ • M₁' a)
    (h₂ : ∀ a, M₂ a = c₂ • M₂' a) (hc : c₂ ≠ 0) (v : C) :
    M₁ (M₂.symm v) = (c₁ / c₂) • M₁' (M₂'.symm v) := by
  have hv : M₂'.symm v = c₂ • M₂.symm v := by
    rw [symm_apply_eq, map_smul, ← h₂, apply_symm_apply]
  rw [h₁, hv, map_smul, smul_smul, div_mul_cancel₀ _ hc]

/-- Coordinate relabelling of function modules is injective in the coordinate equivalence over a
nontrivial target module. -/
theorem funCongrLeft_injective (R M : Type*) [Semiring R] [AddCommMonoid M] [Module R M]
    [Nontrivial M] {ι κ : Type*} :
    Function.Injective (LinearEquiv.funCongrLeft R M : (κ ≃ ι) → (ι → M) ≃ₗ[R] (κ → M)) := by
  classical
  intro e₁ e₂ h
  obtain ⟨m, hm⟩ := exists_ne (0 : M)
  ext j
  by_contra hne
  have hj := congrArg (fun f : (ι → M) ≃ₗ[R] (κ → M) ↦ f (Pi.single (e₁ j) m) j) h
  rw [funCongrLeft_apply, funCongrLeft_apply, LinearMap.funLeft_apply, LinearMap.funLeft_apply,
    Pi.single_eq_same, Pi.single_eq_of_ne (Ne.symm hne)] at hj
  exact hm hj

/-- Every `R`-linear automorphism of a rank-one free `R`-module `ι → R` over a commutative semiring
`R` is scalar multiplication by a unit of `R`. -/
theorem exists_eq_smulOfUnit_of_unique {R ι : Type*} [CommSemiring R] [Unique ι]
    (e : (ι → R) ≃ₗ[R] (ι → R)) : ∃ u : Rˣ, e = LinearEquiv.smulOfUnit u := by
  let φ := LinearEquiv.funUnique ι R R
  let e' : R ≃ₗ[R] R := (φ.symm.trans e).trans φ
  have h1 (f : R →ₗ[R] R) (x : R) : f x = f 1 * x := by
    calc f x = f (x • 1) := by rw [smul_eq_mul, mul_one]
      _ = x • f 1 := f.map_smul x 1
      _ = f 1 * x := by rw [smul_eq_mul, mul_comm]
  refine ⟨⟨e' 1, e'.symm 1, ?_, ?_⟩, ?_⟩
  · rw [← coe_toLinearMap, ← h1]; exact e'.apply_symm_apply 1
  · rw [← coe_toLinearMap, ← h1]; exact e'.symm_apply_apply 1
  · ext x i
    rw [Unique.eq_default i]
    have hval : e x default = φ (e x) := (congrFun (LinearEquiv.funUnique_apply ι R R) (e x)).symm
    have hx : φ (e x) = e' (φ x) := by simp [e']
    rw [hval, hx]
    exact (h1 (e' : R →ₗ[R] R) (φ x)).trans (by simp [φ, smulOfUnit, mul_comm])

/-- Every `ℤ`-linear automorphism of `ι → ℤ` (`Unique ι`) is `id` or `-id`. -/
theorem toLinearMap_eq_id_or_neg_of_unique {ι : Type*} [Unique ι] (e : (ι → ℤ) ≃ₗ[ℤ] (ι → ℤ)) :
    (e : (ι → ℤ) →ₗ[ℤ] (ι → ℤ)) = LinearMap.id ∨ (e : (ι → ℤ) →ₗ[ℤ] (ι → ℤ)) = -LinearMap.id := by
  obtain ⟨u, rfl⟩ := e.exists_eq_smulOfUnit_of_unique
  rcases Int.units_eq_one_or u with rfl | rfl <;>
    [left; right] <;> exact LinearMap.ext fun x => by simp [smulOfUnit]

/-- Conjugating an algebra homomorphism `φ` into `Module.End S M₁` along `e : M₁ ≃ₗ[S] M₂` equals
`ψ` into `Module.End S M₂` exactly when `e` intertwines `φ a` with `ψ a` for every `a`. -/
theorem conjAlgEquiv_toAlgHom_comp_eq_iff {R S A M₁ M₂ : Type*}
    [CommSemiring R] [AddCommMonoid M₁] [Module R M₁] [AddCommMonoid M₂] [Module R M₂]
    [Semiring S] [Module S M₁] [Module S M₂] [SMulCommClass S R M₁] [SMulCommClass S R M₂]
    [SMul R S] [IsScalarTower R S M₁] [IsScalarTower R S M₂]
    [Semiring A] [Algebra R A]
    (e : M₁ ≃ₗ[S] M₂) (φ : A →ₐ[R] Module.End S M₁) (ψ : A →ₐ[R] Module.End S M₂) :
    (e.conjAlgEquiv R).toAlgHom.comp φ = ψ ↔ ∀ a t, e (φ a t) = ψ a (e t) := by
  refine ⟨fun h a t ↦ ?_, fun h ↦ AlgHom.ext fun a ↦ LinearMap.ext fun y ↦ ?_⟩
  · simpa [LinearEquiv.conjAlgEquiv_apply] using
      congrArg (fun f : A →ₐ[R] Module.End S M₂ ↦ f a (e t)) h
  · obtain ⟨t, rfl⟩ := e.surjective y
    simp [LinearEquiv.conjAlgEquiv_apply, h]

end LinearEquiv

namespace Submodule

/-- Following the identification `p ≃ q` of equal submodules by the inclusion of `q` is the
inclusion of `p`. -/
@[simp]
theorem subtype_comp_ofEq {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    {p q : Submodule R M} (h : p = q) :
    q.subtype ∘ₗ (LinearEquiv.ofEq p q h).toLinearMap = p.subtype :=
  LinearMap.ext fun x ↦ LinearEquiv.coe_ofEq_apply h x

end Submodule

namespace LinearMap

section Conjugate

variable {R M N M' N' : Type*} [Ring R]
variable [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
variable [AddCommGroup M'] [Module R M'] [AddCommGroup N'] [Module R N']
variable {f : M →ₗ[R] N} {g : M' →ₗ[R] N'}

/-- Linear maps conjugate under linear equivalences, `e' ∘ f = g ∘ e`, have linearly equivalent
kernels, through `e`. -/
def kerEquivOfComp (e : M ≃ₗ[R] M') (e' : N ≃ₗ[R] N')
    (h : (e' : N →ₗ[R] N') ∘ₗ f = g ∘ₗ (e : M →ₗ[R] M')) : f.ker ≃ₗ[R] g.ker :=
  (e.submoduleMap f.ker).trans <| LinearEquiv.ofEq _ _ <| by
    rw [← LinearEquiv.ker_comp e' f, h, ker_comp,
      Submodule.map_comap_eq_of_surjective e.surjective]

@[simp]
lemma coe_kerEquivOfComp_apply (e : M ≃ₗ[R] M') (e' : N ≃ₗ[R] N')
    (h : (e' : N →ₗ[R] N') ∘ₗ f = g ∘ₗ (e : M →ₗ[R] M')) (x : f.ker) :
    (kerEquivOfComp e e' h x : M') = e x := by
  rfl

/-- Linear maps conjugate under linear equivalences, `e' ∘ f = g ∘ e`, have linearly equivalent
cokernels, through `e'`. -/
def cokerEquivOfComp (e : M ≃ₗ[R] M') (e' : N ≃ₗ[R] N')
    (h : (e' : N →ₗ[R] N') ∘ₗ f = g ∘ₗ (e : M →ₗ[R] M')) : (N ⧸ f.range) ≃ₗ[R] N' ⧸ g.range :=
  Submodule.Quotient.equiv _ _ e' <| by
    rw [← range_comp, h, range_comp_of_range_eq_top _ (range_eq_top.2 e.surjective)]

@[simp]
lemma cokerEquivOfComp_mk (e : M ≃ₗ[R] M') (e' : N ≃ₗ[R] N')
    (h : (e' : N →ₗ[R] N') ∘ₗ f = g ∘ₗ (e : M →ₗ[R] M')) (y : N) :
    cokerEquivOfComp e e' h (Submodule.Quotient.mk y) = Submodule.Quotient.mk (e' y) := by
  rfl

end Conjugate

end LinearMap

namespace RingEquiv

/-- A ring isomorphism over a common target carries the kernel of one map to the kernel of the
other, as a semilinear image. -/
theorem map_ker_toSemilinearEquiv {A B S : Type*} [Semiring A] [Semiring B] [Semiring S]
    (Φ : A ≃+* B) (g : A →+* S) (h : B →+* S)
    (hΦ : ∀ x, h (Φ x) = g x) :
    Submodule.map (Φ.toSemilinearEquiv : A →ₛₗ[(Φ : A →+* B)] B) (RingHom.ker g) =
      RingHom.ker h := by
  have : RingHomInvPair (Φ : A →+* B) (Φ.symm : B →+* A) := .of_ringEquiv Φ
  have : RingHomInvPair (Φ.symm : B →+* A) (Φ : A →+* B) := .of_ringEquiv_symm Φ
  ext y
  rw [Submodule.mem_map_equiv, RingHom.mem_ker, RingHom.mem_ker, ← hΦ]
  exact Iff.of_eq (congrArg (· = 0) (congrArg _ (Φ.apply_symm_apply y)))

end RingEquiv
