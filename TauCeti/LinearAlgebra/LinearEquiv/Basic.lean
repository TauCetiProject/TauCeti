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
public import Mathlib.Logic.Equiv.Fin.Rotate
public import Mathlib.RingTheory.Ideal.Maps
import Mathlib.Algebra.Exact.Basic
import TauCeti.LinearAlgebra.Span.Basic

/-!
# Elementary linear-equivalence transport

Transport of submodule stability through an intertwining semilinear equivalence.
Symmetry of a linear automorphism agrees with inversion in its group structure, and commutes with
restriction of scalars. Integer powers of nonzero scalar multiplication act by integer powers of
the scalar (`LinearEquiv.smulOfNeZero_zpow_apply`), and `LinearEquiv.cyclicShift` shifts `Fin r → V`
cyclically while scaling the wraparound coordinate by `π ≠ 0`.
Given an injective linear map `ι : M →ₗ[R] V` and a linear section of the quotient map
`V →ₗ[R] V ⧸ LinearMap.range ι`, `LinearEquiv.sectionProdEquiv` identifies `M × (V ⧸ range ι)`
with `V`.
Through a linear equivalence `L : M ≃ₗ[R] M₁ × M₂`, the vectors `L⁻¹ (0, vᵢ)` for a spanning
family `v` of `M₂` span the kernel of `u ↦ (L u).1`.
A ring isomorphism over a common target carries the kernel of one map to the kernel of the other.
Composites of rescaled linear equivalences rescale by the quotient of the factors.
Linear maps conjugate under linear equivalences have linearly equivalent kernels and cokernels,
`LinearMap.kerEquivOfComp` and `LinearMap.cokerEquivOfComp`.
Coordinate relabelling of function modules (`LinearEquiv.funCongrLeft`) is injective in the
coordinate equivalence over a nontrivial target module.
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

/-- Integer powers of scalar multiplication by a nonzero element act as scalar multiplication by
the corresponding integer power. -/
@[simp]
theorem smulOfNeZero_zpow_apply {K M : Type*} [Field K] [AddCommGroup M] [Module K M]
    (a : K) (ha : a ≠ 0) (z : ℤ) (x : M) :
    ((LinearEquiv.smulOfNeZero K M a ha) ^ z) x = a ^ z • x := by
  have hz := congrArg (fun e : M ≃ₗ[K] M ↦ e x)
    (map_zpow (DistribMulAction.toModuleAut K M) (Units.mk0 a ha) z)
  simpa [LinearEquiv.smulOfNeZero, LinearEquiv.smulOfUnit, Units.smul_def,
    Units.val_zpow_eq_zpow_val] using hz.symm

/-- Cyclic shift on `Fin r → V` as a linear automorphism, scaling coordinate `0` by `π ≠ 0`. -/
def cyclicShift (R V : Type*) [Field R] [AddCommGroup V] [Module R V]
    (π : R) (hπ : π ≠ 0) (r : ℕ) : (Fin r → V) ≃ₗ[R] (Fin r → V) where
  toFun w i := (if (i : ℕ) = 0 then π else 1) • w ((finRotate r).symm i)
  invFun w j := (if (finRotate r j : ℕ) = 0 then π⁻¹ else 1) • w (finRotate r j)
  left_inv w := by
    ext j
    simp only [Equiv.symm_apply_apply]
    split_ifs <;> simp [smul_smul, hπ]
  right_inv w := by
    ext i
    simp only [Equiv.apply_symm_apply]
    split_ifs <;> simp [smul_smul, hπ]
  map_add' x y := by ext i; simp [smul_add]
  map_smul' c x := by ext i; simp [smul_comm c]

/-- Coordinate formula for `LinearEquiv.cyclicShift`. -/
@[simp]
theorem cyclicShift_apply {R V : Type*} [Field R] [AddCommGroup V] [Module R V]
    (π : R) (hπ : π ≠ 0) (r : ℕ) (w : Fin r → V) (i : Fin r) :
    cyclicShift R V π hπ r w i = (if (i : ℕ) = 0 then π else 1) • w ((finRotate r).symm i) := by
  rfl

/-- Given an injective linear map `ι : M →ₗ[R] V` and a linear section `sec` of the quotient map
`V →ₗ[R] V ⧸ LinearMap.range ι`, `M × (V ⧸ LinearMap.range ι)` is linearly equivalent to `V` via
`(x, y) ↦ ι x + sec y`. -/
noncomputable def sectionProdEquiv {R M V : Type*} [Ring R] [AddCommGroup M] [Module R M]
    [AddCommGroup V] [Module R V] (ι : M →ₗ[R] V) (hι : Function.Injective ι)
    (sec : (V ⧸ LinearMap.range ι) →ₗ[R] V)
    (hq_sec : ∀ y, (LinearMap.range ι).mkQ (sec y) = y) :
    (M × (V ⧸ LinearMap.range ι)) ≃ₗ[R] V :=
  ((LinearMap.exact_iff (f := ι) (g := (LinearMap.range ι).mkQ)).2
    (Submodule.ker_mkQ _) |>.splitSurjectiveEquiv hι
      ⟨sec, LinearMap.ext hq_sec⟩).val.symm

/-- Applying `LinearEquiv.sectionProdEquiv` to `(x, y)` gives `ι x + sec y`. -/
@[simp]
theorem sectionProdEquiv_apply {R M V : Type*} [Ring R] [AddCommGroup M] [Module R M]
    [AddCommGroup V] [Module R V] (ι : M →ₗ[R] V) (hι : Function.Injective ι)
    (sec : (V ⧸ LinearMap.range ι) →ₗ[R] V)
    (hq_sec : ∀ y, (LinearMap.range ι).mkQ (sec y) = y) (p : M × (V ⧸ LinearMap.range ι)) :
    sectionProdEquiv ι hι sec hq_sec p = ι p.1 + sec p.2 := by
  simp [sectionProdEquiv, Function.Exact.splitSurjectiveEquiv]
  rfl

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
