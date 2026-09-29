/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.CrossedProduct.BrauerClass
import Mathlib.FieldTheory.Normal.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.LinearIndependent.Basic
import Mathlib.RingTheory.Trace.Basic

/-!
# Inflating a cocycle along a compatible pair

A **compatible pair** for `2`-cocycles is a homomorphism `f : Aut_K(M) → Aut_K(L)` together with
an embedding `ι : L →ₐ[K] M` intertwining it, `ι (f g x) = g (ι x)`. The pair that matters is
restriction `Gal(M/K) → Gal(L/K)` with the inclusion, for finite Galois extensions `K ⊆ L ⊆ M`.
Along such a pair a `2`-cocycle `c` of `Aut_K(L)` with values in `Lˣ` **inflates** to the cocycle
`c.comap f ι hf : (g, g') ↦ ι (c (f g, f g'))` of `Aut_K(M)`; without the intertwining hypothesis
this function would not be a cocycle, which is why the hypothesis is an argument of
`TauCeti.TwoCocycle.comap`.

The theorem of the file is that inflation does not change the Brauer class of the crossed product.
Write `A = (L, Gal(L/K), c)`, `B = (M, Gal(M/K), c.comap f ι hf)` and `r = [M : L]`. Choose an
`L`-basis `m_i` of `M` and let `m*_i` be the dual basis for the trace form of `M/L`, and let
`ψ : A → B` be the `K`-linear map `x · u_σ ↦ ∑_{f g = σ} ι(x) · u'_g` spreading a coefficient over
the fibre of `f`. Then
`Φ : M_r(A) → B, X ↦ ∑_{i,j} m*_i · ψ(X i j) · m_j`
is an isomorphism of `K`-algebras. It is multiplicative because the fibres of `f` are cosets of the
subgroup `Gal(M/L)`, over which the automorphisms sum to the trace, so that
`ψ(a) · y · ψ(a') = ψ(a · Tr_{M/L}(y) · a')` and `Tr_{M/L}(m_j m*_k) = δ_{jk}`; it is unital by
Dedekind's independence of characters, which gives `∑_i m*_i · g(m_i) = δ_{g,1}` for `g` fixing
`L`; and it is bijective because `M_r(A)` is simple and both sides have dimension `[M : K]²`.

## Main definitions

* `TauCeti.TwoCocycle.comap f ι hf c`: the inflation of `c` along the compatible pair `(f, ι)`.

## Main results

* `TauCeti.TwoCocycle.Cohomologous.comap`: inflation preserves being cohomologous.
* `TauCeti.CrossedProduct.nonempty_algEquiv_matrix_comap`: for a tower `K ⊆ L ⊆ M` of finite
  Galois extensions, the crossed product of the inflated cocycle is isomorphic to the algebra of
  `[M : L] × [M : L]` matrices over the crossed product of `c`.
* `TauCeti.BrauerGroup.crossedProductClass_comap`: **inflation does not change the Brauer class**,
  `[(M, Gal(M/K), c.comap f ι hf)] = [(L, Gal(L/K), c)]`.

## References

* P. Gille and T. Szamuely, *Central Simple Algebras and Galois Cohomology* (2006), §4.4.
* J.-P. Serre, *Local Fields*, GTM 67 (1979), Chapter X.
-/

public section

open groupCohomology

universe u v w

namespace TauCeti

namespace TwoCocycle

variable {K : Type u} [CommSemiring K] {L : Type v} [CommRing L] [Algebra K L]
  {M : Type w} [CommRing M] [Algebra K M]

/-- The **inflation** of a `2`-cocycle `c` of `Aut_K(L)` along a compatible pair: a homomorphism
`f : Aut_K(M) → Aut_K(L)` and an embedding `ι : L → M` intertwining it, `ι (f g x) = g (ι x)`.
Its values are `(g, g') ↦ ι (c (f g, f g'))`; the intertwining hypothesis is what makes this a
cocycle. -/
def comap (f : (M ≃ₐ[K] M) →* (L ≃ₐ[K] L)) (ι : L →ₐ[K] M) (hf : ∀ g x, ι (f g x) = g (ι x))
    (c : TwoCocycle K L) : TwoCocycle K M where
  toFun g g' := Units.map (ι : L →* M) (c.toFun (f g) (f g'))
  isMulCocycle₂ g g' g'' := by
    have hsmul (x : Lˣ) : g • Units.map (ι : L →* M) x = Units.map (ι : L →* M) (f g • x) :=
      Units.ext (by simp [AlgEquiv.smul_units_def, hf])
    have h := c.isMulCocycle₂ (f g) (f g') (f g'')
    dsimp only at h ⊢
    rw [← map_mul f, ← map_mul f] at h
    rw [hsmul, ← map_mul, ← map_mul, h]

variable (f : (M ≃ₐ[K] M) →* (L ≃ₐ[K] L)) (ι : L →ₐ[K] M) (hf : ∀ g x, ι (f g x) = g (ι x))

/-- The defining equation of the inflated cocycle, `(c.comap f ι hf)(g, g') = ι (c (f g, f g'))`,
as units. -/
theorem comap_toFun (c : TwoCocycle K L) (g g' : M ≃ₐ[K] M) :
    (c.comap f ι hf).toFun g g' = Units.map (ι : L →* M) (c.toFun (f g) (f g')) :=
  (rfl)

/-- The values of the inflated cocycle, `(c.comap f ι hf)(g, g') = ι (c (f g, f g'))`. -/
@[simp]
theorem coe_comap_toFun (c : TwoCocycle K L) (g g' : M ≃ₐ[K] M) :
    ((c.comap f ι hf).toFun g g' : M) = ι (c.toFun (f g) (f g')) :=
  (rfl)

/-- Inflation preserves being cohomologous: if `w / z` is the coboundary of `b`, then the
inflation of `w / z` is the coboundary of `g ↦ ι (b (f g))`. -/
theorem Cohomologous.comap {z w : TwoCocycle K L} (h : z.Cohomologous w) :
    (z.comap f ι hf).Cohomologous (w.comap f ι hf) := by
  obtain ⟨b, hb⟩ := cohomologous_iff.1 h
  refine cohomologous_iff.2 ⟨fun g ↦ Units.map (ι : L →* M) (b (f g)), fun g g' ↦ ?_⟩
  simp [hb, ← hf]

end TwoCocycle

namespace CrossedProduct

open Module

section Tower

variable {K : Type u} [Field K] {L : Type v} [Field L] [Algebra K L] {M : Type w} [Field M]
  [Algebra K M] [Algebra L M] [IsScalarTower K L M] [FiniteDimensional K M]
  (f : (M ≃ₐ[K] M) →* (L ≃ₐ[K] L))
  (hf : ∀ g x, IsScalarTower.toAlgHom K L M (f g x) = g (IsScalarTower.toAlgHom K L M x))

include hf in
/-- The automorphisms in the fibre of `f` over `σ` sum to `σ` followed by the trace of `M/L`. -/
private theorem sum_fiber_apply [IsGalois K M] [DecidableEq (L ≃ₐ[K] L)] (σ : L ≃ₐ[K] L)
    (z : M) :
    ∑ g ∈ Finset.univ.filter (fun g ↦ f g = σ), g z =
      algebraMap L M (σ (Algebra.trace L M z)) := by
  have hf : ∀ g x, algebraMap L M (f g x) = g (algebraMap L M x) := hf
  have : FiniteDimensional L M := Module.Finite.of_restrictScalars_finite K L M
  have : IsGalois L M := IsGalois.tower_top_of_isGalois K L M
  set g₀ := σ.liftNormal M
  have hg₀ : f g₀ = σ := AlgEquiv.ext fun x ↦
    (algebraMap L M).injective ((hf g₀ x).trans (σ.liftNormal_commutes M x))
  -- `f` is trivial exactly on the automorphisms fixing `L`
  have hker (g : M ≃ₐ[K] M) : f g = 1 ↔ ∀ x, g (algebraMap L M x) = algebraMap L M x := by
    refine ⟨fun h x ↦ by rw [← hf, h, AlgEquiv.one_apply], fun h ↦ AlgEquiv.ext fun x ↦
      (algebraMap L M).injective ?_⟩
    rw [hf, h, AlgEquiv.one_apply]
  have hfix (g : M ≃ₐ[K] M) (hg : f g = σ) (x : L) :
      (g₀⁻¹ * g) (algebraMap L M x) = algebraMap L M x :=
    (hker _).1 (by rw [map_mul, map_inv, hg, hg₀, inv_mul_cancel]) x
  calc ∑ g ∈ Finset.univ.filter (fun g ↦ f g = σ), g z
      = ∑ τ : Gal(M/L), g₀ (τ z) := by
        symm
        refine Finset.sum_bij' (fun τ _ ↦ g₀ * τ.restrictScalars K)
          (fun g hg ↦ AlgEquiv.ofRingEquiv (f := (g₀⁻¹ * g).toRingEquiv)
            (hfix g (Finset.mem_filter.1 hg).2)) (fun τ _ ↦ ?_) (fun _ _ ↦ Finset.mem_univ _)
          (fun τ _ ↦ ?_) (fun g _ ↦ ?_) (fun τ _ ↦ rfl)
        · rw [Finset.mem_filter, map_mul, hg₀, (hker _).2 τ.commutes, mul_one]
          exact ⟨Finset.mem_univ _, rfl⟩
        · ext x
          simp
        · ext x
          simp
    _ = algebraMap L M (σ (Algebra.trace L M z)) := by
        rw [← map_sum, ← trace_eq_sum_automorphisms, ← hf, hg₀]

variable (c : TwoCocycle K L)

/-- The `K`-linear map `a ↦ ∑_g a_{f g} · u_g`, spreading the coefficient of `u_σ` over the fibre of
`f` above `σ`. -/
private noncomputable def fiberMap :
    CrossedProduct c →ₗ[K] CrossedProduct (c.comap f (IsScalarTower.toAlgHom K L M) hf) where
  toFun a := ∑ g, algebraMap L M ((basis c).repr a (f g)) • basis _ g
  map_add' a b := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' r a := by
    rw [RingHom.id_apply, Finset.smul_sum]
    refine Finset.sum_congr rfl fun g _ ↦ ?_
    rw [← algebraMap_smul L r a, map_smul, Finsupp.smul_apply, smul_eq_mul, map_mul,
      ← IsScalarTower.algebraMap_apply, mul_smul, algebraMap_smul]

variable {f hf c}

private theorem fiberMap_apply (a : CrossedProduct c) :
    fiberMap f hf c a = ∑ g, algebraMap L M ((basis c).repr a (f g)) • basis _ g :=
  (rfl)

private theorem fiberMap_smul_basis [DecidableEq (L ≃ₐ[K] L)] (σ : L ≃ₐ[K] L) (x : L) :
    fiberMap f hf c (x • basis c σ) =
      ∑ g ∈ Finset.univ.filter (fun g ↦ f g = σ), algebraMap L M x • basis _ g := by
  rw [fiberMap_apply, Finset.sum_filter]
  refine Finset.sum_congr rfl fun g _ ↦ ?_
  rw [map_smul, Module.Basis.repr_self, Finsupp.smul_single, smul_eq_mul, mul_one,
    Finsupp.single_apply]
  by_cases h : f g = σ <;> simp [h, Ne.symm]

/-- The multiplication rule behind the matrix decomposition: sandwiching `u'_y` between two images
of `fiberMap` is `fiberMap` of the product sandwiching the trace of `y`. -/
private theorem fiberMap_mul_inc_mul [IsGalois K M] (a a' : CrossedProduct c) (y : M) :
    fiberMap f hf c a * inc _ y * fiberMap f hf c a' =
      fiberMap f hf c (a * inc c (Algebra.trace L M y) * a') := by
  classical
  have hf' : ∀ g x, algebraMap L M (f g x) = g (algebraMap L M x) := hf
  induction a using induction_on with
  | zero => simp
  | add a₁ a₂ h₁ h₂ => simp only [map_add, add_mul, h₁, h₂]
  | smul_basis σ x =>
  induction a' using induction_on with
  | zero => simp
  | add a₁ a₂ h₁ h₂ => simp only [map_add, mul_add, h₁, h₂]
  | smul_basis τ x' =>
    set F : (L ≃ₐ[K] L) → Finset (M ≃ₐ[K] M) := fun σ ↦ Finset.univ.filter (fun g ↦ f g = σ)
    have hF (g : M ≃ₐ[K] M) (σ : L ≃ₐ[K] L) : g ∈ F σ ↔ f g = σ := by simp [F]
    set C := algebraMap L M (x * σ x' * c.toFun σ τ)
    calc fiberMap f hf c (x • basis c σ) * inc _ y * fiberMap f hf c (x' • basis c τ)
        = ∑ g ∈ F σ, ∑ g' ∈ F τ, (C * g y) • basis _ (g * g') := by
          rw [fiberMap_smul_basis, fiberMap_smul_basis, Finset.sum_mul, Finset.sum_mul]
          refine Finset.sum_congr rfl fun g hg ↦ ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun g' hg' ↦ ?_
          rw [smul_mul_assoc, basis_mul_inc, ← smul_def, smul_smul, smul_basis_mul_smul_basis,
            TwoCocycle.coe_comap_toFun, IsScalarTower.coe_toAlgHom', ← hf', (hF g σ).1 hg,
            (hF g' τ).1 hg']
          congr 1
          simp only [C, map_mul]
          ring
      _ = ∑ g ∈ F σ, ∑ k ∈ F (σ * τ), (C * g y) • basis _ k := by
          refine Finset.sum_congr rfl fun g hg ↦ ?_
          refine Finset.sum_nbij' (fun g' ↦ g * g') (fun k ↦ g⁻¹ * k) (fun g' hg' ↦ ?_)
            (fun k hk ↦ ?_) (fun g' _ ↦ inv_mul_cancel_left g g')
            (fun k _ ↦ mul_inv_cancel_left g k) (fun _ _ ↦ rfl)
          · rw [hF, map_mul, (hF g σ).1 hg, (hF g' τ).1 hg']
          · rw [hF, map_mul, map_inv, (hF g σ).1 hg, (hF k _).1 hk, inv_mul_cancel_left]
      _ = ∑ k ∈ F (σ * τ), (C * ∑ g ∈ F σ, g y) • basis _ k := by
          rw [Finset.sum_comm]
          simp only [Finset.mul_sum, Finset.sum_smul]
      _ = fiberMap f hf c (x • basis c σ * inc c (Algebra.trace L M y) * x' • basis c τ) := by
          rw [smul_mul_assoc, basis_mul_inc, ← smul_def, smul_smul, smul_basis_mul_smul_basis,
            fiberMap_smul_basis]
          refine Finset.sum_congr rfl fun k _ ↦ ?_
          rw [sum_fiber_apply f hf σ y]
          congr 1
          simp only [C, map_mul]
          ring

section Dual

variable [FiniteDimensional L M] [Algebra.IsSeparable L M] {ι : Type*} [Fintype ι]
  [DecidableEq ι] (m : Basis ι L M)

open Classical in
variable (f hf) in
include hf in
/-- For `g` fixing `L`, `∑ᵢ m*ᵢ · g(mᵢ)` is `1` if `g = 1` and `0` otherwise. This is Dedekind's
independence of characters applied to `x = ∑ᵢ m*ᵢ · Tr(mᵢ x) = ∑_g (∑ᵢ m*ᵢ · g(mᵢ)) · g(x)`. -/
private theorem sum_traceDual_mul_apply [IsGalois K M] (g : M ≃ₐ[K] M) (hg : f g = 1) :
    ∑ i, m.traceDual i * g (m i) = if g = 1 then 1 else 0 := by
  classical
  set C : (M ≃ₐ[K] M) → M := fun g ↦ if f g = 1 then ∑ i, m.traceDual i * g (m i) else 0
  have hC (x : M) : ∑ g, C g * g x = x := by
    calc ∑ g, C g * g x
        = ∑ g ∈ Finset.univ.filter (fun g ↦ f g = 1), ∑ i, m.traceDual i * g (m i * x) := by
          rw [Finset.sum_filter]
          refine Finset.sum_congr rfl fun g _ ↦ ?_
          simp only [C]
          split_ifs <;> simp [Finset.sum_mul, map_mul, mul_assoc]
      _ = ∑ i, m.traceDual i * ∑ g ∈ Finset.univ.filter (fun g ↦ f g = 1), g (m i * x) := by
          rw [Finset.sum_comm]
          simp only [Finset.mul_sum]
      _ = ∑ i, Algebra.trace L M (x * m i) • m.traceDual i := by
          refine Finset.sum_congr rfl fun i _ ↦ ?_
          rw [sum_fiber_apply f hf, AlgEquiv.one_apply, Algebra.smul_def, mul_comm, mul_comm x]
      _ = x := by
          conv_rhs => rw [← m.traceDual.sum_repr x]
          simp [Algebra.traceForm_apply]
  have hli := (linearIndependent_monoidHom M M).comp (fun g : M ≃ₐ[K] M ↦ (g : M →* M))
    fun g g' h ↦ AlgEquiv.ext fun x ↦ by simpa using DFunLike.congr_fun h x
  have := Fintype.linearIndependent_iffₛ.1 hli C (fun g ↦ if g = 1 then 1 else 0) (by
    funext x
    simp [Finset.sum_apply, hC, ite_apply])
  simpa [C, hg] using this g

variable (f hf c) in
/-- The `K`-linear map `X ↦ ∑_{i,j} m*ᵢ · fiberMap(X i j) · mⱼ`, which is the matrix decomposition
of the crossed product of the inflated cocycle. -/
private noncomputable def matrixLinearMap : Matrix ι ι (CrossedProduct c) →ₗ[K]
    CrossedProduct (c.comap f (IsScalarTower.toAlgHom K L M) hf) where
  toFun X := ∑ i, ∑ j, inc _ (m.traceDual i) * fiberMap f hf c (X i j) * inc _ (m j)
  map_add' X Y := by simp [mul_add, add_mul, Finset.sum_add_distrib]
  map_smul' r X := by simp [Finset.smul_sum]

private theorem matrixLinearMap_apply (X : Matrix ι ι (CrossedProduct c)) :
    matrixLinearMap f hf c m X =
      ∑ i, ∑ j, inc _ (m.traceDual i) * fiberMap f hf c (X i j) * inc _ (m j) :=
  (rfl)

private theorem matrixLinearMap_mul [IsGalois K M] (X Y : Matrix ι ι (CrossedProduct c)) :
    matrixLinearMap f hf c m (X * Y) =
      matrixLinearMap f hf c m X * matrixLinearMap f hf c m Y := by
  have key (i j k l : ι) : inc _ (m.traceDual i) * fiberMap f hf c (X i j) * inc _ (m j) *
      (inc _ (m.traceDual k) * fiberMap f hf c (Y k l) * inc _ (m l)) =
      if j = k then inc _ (m.traceDual i) * fiberMap f hf c (X i j * Y j l) * inc _ (m l)
      else 0 := by
    calc _ = inc _ (m.traceDual i) * (fiberMap f hf c (X i j) * inc _ (m j * m.traceDual k) *
          fiberMap f hf c (Y k l)) * inc _ (m l) := by
          simp only [map_mul, mul_assoc]
      _ = _ := by
          rw [fiberMap_mul_inc_mul, Module.Basis.trace_mul_traceDual]
          split_ifs with h
          · subst h
            rw [map_one, mul_one]
          · rw [map_zero, mul_zero, zero_mul, map_zero, mul_zero, zero_mul]
  simp only [matrixLinearMap_apply, Matrix.mul_apply, map_sum, Finset.sum_mul, Finset.mul_sum,
    key, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  -- both sides are now the same triple sum over `(i, j, l)`, in different orders
  refine (Finset.sum_congr rfl fun i _ ↦ Finset.sum_comm).trans ?_
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ ↦ Finset.sum_comm

private theorem matrixLinearMap_one [IsGalois K M] : matrixLinearMap f hf c m 1 = 1 := by
  classical
  set F := Finset.univ.filter (fun g : M ≃ₐ[K] M ↦ f g = 1)
  set z := algebraMap L M (((c.toFun 1 1)⁻¹ : Lˣ) : L)
  calc matrixLinearMap f hf c m 1
      = ∑ i, inc _ (m.traceDual i) * fiberMap f hf c 1 * inc _ (m i) := by
        simp [matrixLinearMap_apply, Matrix.one_apply, apply_ite, ite_mul]
    _ = ∑ g ∈ F, (z * ∑ i, m.traceDual i * g (m i)) • basis _ g := by
        rw [one_def, fiberMap_smul_basis]
        simp only [Finset.mul_sum, Finset.sum_mul, Finset.sum_smul]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun g _ ↦ Finset.sum_congr rfl fun i _ ↦ ?_
        rw [← smul_def, smul_smul, smul_mul_assoc, basis_mul_inc, ← smul_def, smul_smul]
        congr 1
        ring
    _ = z • basis _ 1 := by
        rw [Finset.sum_congr rfl fun g hg ↦ by
          rw [sum_traceDual_mul_apply f hf m g (Finset.mem_filter.1 hg).2, mul_ite, mul_one,
            mul_zero, ite_smul, zero_smul]]
        rw [Finset.sum_ite_eq']
        simp [F]
    _ = 1 := by
        rw [one_def]
        simp [z]

end Dual

variable (f hf) in
/-- **The crossed product of an inflated cocycle is a matrix algebra over the crossed product.**
For finite Galois extensions `K ⊆ L ⊆ M` and `f : Gal(M/K) → Gal(L/K)` compatible with the
inclusion `L ⊆ M`, the crossed product of `c.comap f` is isomorphic to the algebra of
`[M : L] × [M : L]` matrices over the crossed product of `c`. -/
theorem nonempty_algEquiv_matrix_comap [IsGalois K M] [IsGalois K L] (c : TwoCocycle K L) :
    Nonempty (CrossedProduct (c.comap f (IsScalarTower.toAlgHom K L M) hf) ≃ₐ[K]
      Matrix (Fin (finrank L M)) (Fin (finrank L M)) (CrossedProduct c)) := by
  have : FiniteDimensional K L := Module.Finite.left K L M
  have : FiniteDimensional L M := Module.Finite.of_restrictScalars_finite K L M
  have : IsGalois L M := IsGalois.tower_top_of_isGalois K L M
  have : NeZero (finrank L M) := ⟨Module.finrank_pos.ne'⟩
  let Φ := AlgHom.ofLinearMap (matrixLinearMap f hf c (Module.finBasis L M))
    (matrixLinearMap_one (Module.finBasis L M)) (matrixLinearMap_mul (Module.finBasis L M))
  have hinj : Function.Injective Φ := Φ.toRingHom.injective
  have hrank : finrank K (Matrix (Fin (finrank L M)) (Fin (finrank L M)) (CrossedProduct c)) =
      finrank K (CrossedProduct (c.comap f (IsScalarTower.toAlgHom K L M) hf)) := by
    rw [Module.finrank_matrix, finrank_eq_finrank_sq, finrank_eq_finrank_sq, Fintype.card_fin,
      ← Module.finrank_mul_finrank K L M]
    ring
  exact ⟨(AlgEquiv.ofBijective Φ ⟨hinj,
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hrank (f := Φ.toLinearMap)).1
      hinj⟩).symm⟩

end Tower

end CrossedProduct

namespace BrauerGroup

variable {K : Type u} [Field K] {L M : Type v} [Field L] [Field M] [Algebra K L] [Algebra K M]
  [FiniteDimensional K L] [IsGalois K L] [FiniteDimensional K M] [IsGalois K M]

/-- **Inflation does not change the Brauer class.** For finite Galois extensions `L/K` and `M/K`,
an embedding `ι : L → M` and a homomorphism `f : Gal(M/K) → Gal(L/K)` intertwined by it, the
cocycle `c.comap f ι hf` of `M/K` presents the same Brauer class as `c`. -/
theorem crossedProductClass_comap (f : (M ≃ₐ[K] M) →* (L ≃ₐ[K] L)) (ι : L →ₐ[K] M)
    (hf : ∀ g x, ι (f g x) = g (ι x)) (c : TwoCocycle K L) :
    crossedProductClass (c.comap f ι hf) = crossedProductClass c := by
  let : Algebra L M := ι.toRingHom.toAlgebra
  have : IsScalarTower K L M := IsScalarTower.of_algebraMap_eq fun x ↦ (ι.commutes x).symm
  have : FiniteDimensional L M := Module.Finite.of_restrictScalars_finite K L M
  have : NeZero (Module.finrank L M) := ⟨Module.finrank_pos.ne'⟩
  obtain ⟨e⟩ := CrossedProduct.nonempty_algEquiv_matrix_comap f hf c
  rw [crossedProductClass_def, crossedProductClass_def,
    ← mk_matrix (CSA.of K (CrossedProduct c)) (Module.finrank L M)]
  exact mk_eq_mk_of_algEquiv e

end BrauerGroup

end TauCeti
