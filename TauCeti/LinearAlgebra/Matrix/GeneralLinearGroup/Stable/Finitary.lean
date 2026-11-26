/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic
public import TauCeti.LinearAlgebra.Finsupp.CoordinateInclusion
public import TauCeti.LinearAlgebra.Finsupp.Supported
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Stable
public import TauCeti.LinearAlgebra.Matrix.ToLin

/-!
# `GL_∞(A)` as the finitary automorphisms of the countable free module

For a possibly noncommutative ring `A`, let `A^(ℕ) = ℕ →₀ A` be the free right `A`-module on the
basis vectors `eₖ = Finsupp.single k 1`, written as a left module over `Aᵐᵒᵖ`. An invertible
matrix `u : GL (Fin n) A` acts on `A^(ℕ)` by matrix multiplication on the first `n` coordinates of
a column vector and by the identity on the remaining ones; this commutes with right scalar
multiplication, and column `j` of `u` is the image of `eⱼ`. The action is compatible with the
stabilizations `u ↦ u ⊕ 1`, so it defines a homomorphism

  `TauCeti.StableGeneralLinearGroup.toFreeModuleAut A : GL_∞(A) →* Aut_{A}(A^(ℕ))`.

An automorphism `g` of `A^(ℕ)` is **finitary** when there is a finite set `s ⊆ ℕ` such that `g`
fixes every basis vector `eₖ` with `k ∉ s` and maps the basis vectors `eₖ` with `k ∈ s` into the
coordinate submodule spanned by `{eᵢ | i ∈ s}`. Over any semiring `A` the finitary
automorphisms form a subgroup `TauCeti.finitaryAutomorphisms A`; closure under inverses holds
because `g` restricts to a bijection of that coordinate submodule. The main result identifies
`GL_∞(A)` with this subgroup: the action is injective, and its image consists exactly of the
finitary automorphisms, a finitary automorphism being the image of the invertible matrix formed by
the coordinates of the `g eⱼ` with `i, j` below a bound for `s`.

This is the classical description of `GL(A)` as the automorphisms of the free module `A^∞` that
are the identity outside a finitely generated free summand.

## Main definitions

* `TauCeti.finitaryAutomorphisms A`: the subgroup of finitary automorphisms of `ℕ →₀ A`.
* `TauCeti.StableGeneralLinearGroup.toFreeModuleAut A`: the action of `GL_∞(A)` on `ℕ →₀ A`.
* `TauCeti.StableGeneralLinearGroup.finitaryAutomorphismsEquiv A`: the isomorphism of `GL_∞(A)`
  with `TauCeti.finitaryAutomorphisms A`.

## Main results

* `TauCeti.StableGeneralLinearGroup.toFreeModuleAut_of_apply_apply`,
  `TauCeti.StableGeneralLinearGroup.toFreeModuleAut_of_apply_single`: the coordinates of the
  action of an invertible matrix, and its value on a basis vector (the corresponding column).
* `TauCeti.StableGeneralLinearGroup.toFreeModuleAut_stableTransvection_apply_single`: the
  elementary matrix `e_{ij}(a)` sends `eⱼ b` to `eⱼ b + eᵢ (a b)` and fixes the other `eₖ b`.
* `TauCeti.StableGeneralLinearGroup.toFreeModuleAut_injective`: the action is faithful.
* `TauCeti.StableGeneralLinearGroup.range_toFreeModuleAut`: its image is
  `TauCeti.finitaryAutomorphisms A`.

## References

* J. Milnor, *Introduction to Algebraic K-Theory*, Annals of Mathematics Studies 72 (1971), §3.
* J. Rosenberg, *Algebraic K-Theory and Its Applications*, GTM 147 (1994), §2.1.
* C. A. Weibel, *The K-book: An Introduction to Algebraic K-Theory*, Graduate Studies in
  Mathematics 145 (2013), Chapter III, §1.
-/

public section

noncomputable section

open Finsupp Matrix MulOpposite

namespace TauCeti

variable (A : Type*)

section Semiring

variable [Semiring A]

/-! ## Linear maps of the countable free module -/

section FreeModule

variable {A}

/-- `f` fixes the basis vectors `eₖ` with `k ∉ s` and maps those with `k ∈ s` into the
coordinate submodule of `s`. -/
private def IsFinitaryOn (f : (ℕ →₀ A) →ₗ[Aᵐᵒᵖ] (ℕ →₀ A)) (s : Set ℕ) : Prop :=
  (∀ k ∉ s, f (single k 1) = single k 1) ∧ ∀ k ∈ s, f (single k 1) ∈ supported A Aᵐᵒᵖ s

private theorem IsFinitaryOn.mono {f : (ℕ →₀ A) →ₗ[Aᵐᵒᵖ] (ℕ →₀ A)} {s t : Set ℕ}
    (hf : IsFinitaryOn f s) (hst : s ⊆ t) : IsFinitaryOn f t := by
  refine ⟨fun k hk ↦ hf.1 k fun hks ↦ hk (hst hks), fun k hk ↦ ?_⟩
  by_cases hks : k ∈ s
  · exact supported_mono hst (hf.2 k hks)
  · rw [hf.1 k hks]
    exact single_mem_supported _ _ hk

/-- A map finitary for `s` preserves the coordinate submodule of `s`. -/
private theorem IsFinitaryOn.map_mem_supported {f : (ℕ →₀ A) →ₗ[Aᵐᵒᵖ] (ℕ →₀ A)} {s : Set ℕ}
    (hf : IsFinitaryOn f s) {x : ℕ →₀ A} (hx : x ∈ supported A Aᵐᵒᵖ s) :
    f x ∈ supported A Aᵐᵒᵖ s :=
  map_mem_supported_of_forall_single_mem Aᵐᵒᵖ f
    (fun k hk a ↦ map_single_eq_op_smul f k a ▸ Submodule.smul_mem _ _ (hf.2 k hk)) hx

/-- A map finitary for `s` fixes every vector supported outside `s`. -/
private theorem IsFinitaryOn.map_eq_self {f : (ℕ →₀ A) →ₗ[Aᵐᵒᵖ] (ℕ →₀ A)} {s : Set ℕ}
    (hf : IsFinitaryOn f s) {x : ℕ →₀ A} (hx : x ∈ supported A Aᵐᵒᵖ sᶜ) : f x = x :=
  map_eq_self_of_forall_single_eq Aᵐᵒᵖ f
    (fun k hk a ↦ by rw [map_single_eq_op_smul, hf.1 k hk, op_smul_single_one]) hx

private theorem IsFinitaryOn.comp {f g : (ℕ →₀ A) →ₗ[Aᵐᵒᵖ] (ℕ →₀ A)} {s : Set ℕ}
    (hf : IsFinitaryOn f s) (hg : IsFinitaryOn g s) : IsFinitaryOn (f ∘ₗ g) s :=
  ⟨fun k hk ↦ by rw [LinearMap.comp_apply, hg.1 k hk, hf.1 k hk],
    fun k hk ↦ hf.map_mem_supported (hg.2 k hk)⟩

/-- The inverse of a finitary automorphism is finitary for the same set: an automorphism fixing
the vectors supported outside `s` and preserving the coordinate submodule of `s` restricts to a
bijection of that submodule. -/
private theorem IsFinitaryOn.symm {g : (ℕ →₀ A) ≃ₗ[Aᵐᵒᵖ] (ℕ →₀ A)} {s : Set ℕ}
    (hg : IsFinitaryOn (g : (ℕ →₀ A) →ₗ[Aᵐᵒᵖ] (ℕ →₀ A)) s) :
    IsFinitaryOn (g.symm : (ℕ →₀ A) →ₗ[Aᵐᵒᵖ] (ℕ →₀ A)) s := by
  refine ⟨fun k hk ↦ g.symm_apply_eq.2 (hg.1 k hk).symm, fun k hk ↦ ?_⟩
  -- Split `y = g⁻¹ eₖ` into its parts supported on `s` and off `s`.
  have hsup : supported A Aᵐᵒᵖ s ⊔ supported A Aᵐᵒᵖ sᶜ = ⊤ :=
    codisjoint_iff.1 (codisjoint_supported_supported isCompl_compl.codisjoint)
  obtain ⟨y₁, hy₁, y₂, hy₂, hy⟩ :=
    Submodule.mem_sup.1 (hsup ▸ Submodule.mem_top : g.symm (single k 1) ∈ _)
  -- `g` fixes `y₂`, so `g y₁ + y₂ = eₖ`; off `s` both `g y₁` and `eₖ` vanish, so `y₂ = 0`.
  have hgy₂ : g y₂ = y₂ := by simpa using hg.map_eq_self hy₂
  have hgy : g y₁ + y₂ = single k 1 := by simpa [hgy₂] using congr(g $hy)
  have hy₂0 : y₂ = 0 := by
    ext i
    by_cases hi : i ∈ s
    · exact (mem_supported' _ _).1 hy₂ i fun hi' ↦ hi' hi
    · have hgy₁ : g y₁ i = 0 := (mem_supported' _ _).1 (hg.map_mem_supported hy₁) i hi
      have := congr($hgy i)
      rwa [Finsupp.add_apply, hgy₁, zero_add,
        single_eq_of_ne fun (hik : i = k) ↦ hi (hik ▸ hk)] at this
  subst hy₂0
  simpa [← hy] using hy₁

end FreeModule

/-! ## Finitary automorphisms -/

/-- The **finitary automorphisms** of the free right `A`-module `ℕ →₀ A`: the right-linear
automorphisms `g` for which there is a finite set `s ⊆ ℕ` such that `g` fixes each basis vector
`eₖ = single k 1` with `k ∉ s` and sends each `eₖ` with `k ∈ s` into the coordinate submodule of
`s`. They form a subgroup. -/
def finitaryAutomorphisms : Subgroup ((ℕ →₀ A) ≃ₗ[Aᵐᵒᵖ] (ℕ →₀ A)) where
  carrier := {g | ∃ s : Finset ℕ, IsFinitaryOn (g : (ℕ →₀ A) →ₗ[Aᵐᵒᵖ] (ℕ →₀ A)) s}
  one_mem' := ⟨∅, by simp [IsFinitaryOn]⟩
  mul_mem' := by
    rintro g h ⟨s, hs⟩ ⟨t, ht⟩
    refine ⟨s ∪ t, ?_⟩
    rw [LinearEquiv.coe_toLinearMap_mul, Module.End.mul_eq_comp]
    exact (hs.mono (by simp)).comp (ht.mono (by simp))
  inv_mem' := by
    rintro g ⟨s, hs⟩
    exact ⟨s, hs.symm⟩

variable {A} in
/-- Membership in the finitary automorphisms, with a finite set of exceptional basis vectors. -/
theorem mem_finitaryAutomorphisms_iff {g : (ℕ →₀ A) ≃ₗ[Aᵐᵒᵖ] (ℕ →₀ A)} :
    g ∈ finitaryAutomorphisms A ↔ ∃ s : Finset ℕ, (∀ k ∉ s, g (single k 1) = single k 1) ∧
      ∀ k ∈ s, g (single k 1) ∈ supported A Aᵐᵒᵖ (s : Set ℕ) :=
  Iff.rfl

/-! ## Coordinates on the first `n` basis vectors -/

section Coordinates

variable {A}

/-- The matrix of the values of a right-linear map on the basis vectors `e₀, …, e_{n-1}`,
truncated to the first `n` coordinates. -/
private def coordMatrix (f : (ℕ →₀ A) →ₗ[Aᵐᵒᵖ] (ℕ →₀ A)) (n : ℕ) : Matrix (Fin n) (Fin n) A :=
  Matrix.of fun i j ↦ f (single j 1) i

/-- Truncated coordinate matrices multiply when the second map preserves the first `n`
coordinates. -/
private theorem coordMatrix_mul (f : (ℕ →₀ A) →ₗ[Aᵐᵒᵖ] (ℕ →₀ A))
    {f' : (ℕ →₀ A) →ₗ[Aᵐᵒᵖ] (ℕ →₀ A)} {n : ℕ}
    (hf' : ∀ k ∈ (Finset.range n : Set ℕ), f' (single k 1) ∈ supported A Aᵐᵒᵖ ↑(Finset.range n)) :
    coordMatrix f n * coordMatrix f' n = coordMatrix (f ∘ₗ f') n := by
  ext i j
  simp only [Matrix.mul_apply, coordMatrix, Matrix.of_apply, LinearMap.comp_apply]
  rw [map_apply_eq_sum_of_mem_supported f (hf' j (by simp))]

private theorem coordMatrix_id (n : ℕ) :
    coordMatrix (LinearMap.id : Module.End Aᵐᵒᵖ (ℕ →₀ A)) n = 1 := by
  ext i j
  simp [coordMatrix, Matrix.one_apply, Finsupp.single_apply, Fin.ext_iff, eq_comm]

end Coordinates

end Semiring

/-! ## The action of invertible matrices -/

variable [Ring A]

section Action

variable {A}

/-- The endomorphism `1 + ι (M - 1) π` of `ℕ →₀ A`, where `π` restricts to the first `n`
coordinates and `ι` embeds them back: `M` acts on the first `n` coordinates of a column vector and
the identity on the others. -/
private def cornerEnd (n : ℕ) : Matrix (Fin n) (Fin n) A →* Module.End Aᵐᵒᵖ (ℕ →₀ A) where
  toFun M := 1 + coordinateInclusion n ∘ₗ mulVecBilin A Aᵐᵒᵖ (M - 1) ∘ₗ coordinateRestriction n
  map_one' := by simp
  map_mul' M N := by
    -- `X ↦ ι X π` is multiplicative because `π ι = 1`.
    set e : Module.End Aᵐᵒᵖ (Fin n → A) → Module.End Aᵐᵒᵖ (ℕ →₀ A) :=
      fun X ↦ coordinateInclusion n ∘ₗ X ∘ₗ coordinateRestriction n with he
    have hadd (X Y) : e (X + Y) = e X + e Y := by
      simp [he, LinearMap.comp_add, LinearMap.add_comp]
    have hmul (X Y) : e X * e Y = e (X * Y) := by
      have hπι (Z : (ℕ →₀ A) →ₗ[Aᵐᵒᵖ] (Fin n → A)) :
          coordinateRestriction n ∘ₗ coordinateInclusion n ∘ₗ Z = Z := by
        rw [← LinearMap.comp_assoc, coordinateRestriction_comp_coordinateInclusion,
          LinearMap.id_comp]
      simp only [he, Module.End.mul_eq_comp, LinearMap.comp_assoc, hπι]
    set φ := mulVecBilin A Aᵐᵒᵖ (m := Fin n) (n := Fin n) (A := A)
    have hφ1 : φ 1 = 1 := LinearMap.ext fun v ↦ one_mulVec v
    have hφmul (X Y) : φ (X * Y) = φ X * φ Y := mulVecBilin_mul X Y
    -- `set` does not abstract `e` and `φ` inside the unfolded `toFun`; restate the goal with them.
    change 1 + e (φ (M * N - 1)) = (1 + e (φ (M - 1))) * (1 + e (φ (N - 1)))
    have key : φ M * φ N - 1 = (φ M - 1) + (φ N - 1) + (φ M - 1) * (φ N - 1) := by
      simp only [sub_mul, mul_sub, one_mul, mul_one]
      abel
    rw [map_sub, map_sub, map_sub, hφ1, hφmul, key, hadd, hadd, ← hmul]
    simp only [add_mul, mul_add, one_mul, mul_one]
    abel

/-- The coordinates of `cornerEnd n M v`. -/
private theorem cornerEnd_apply_apply (n : ℕ) (M : Matrix (Fin n) (Fin n) A) (v : ℕ →₀ A)
    (i : ℕ) :
    cornerEnd n M v i = if h : i < n then ∑ j : Fin n, M ⟨i, h⟩ j * v j else v i := by
  simp only [cornerEnd, MonoidHom.coe_mk, OneHom.coe_mk, LinearMap.add_apply, one_apply_eq_self,
    LinearMap.comp_apply, mulVecBilin_apply, Finsupp.add_apply, coordinateInclusion_apply]
  split_ifs with h
  · rw [sub_mulVec, one_mulVec, Pi.sub_apply, coordinateRestriction_apply]
    simp only [mulVec, dotProduct, coordinateRestriction_apply]
    abel
  · rw [add_zero]

/-- The action of `GL (Fin n) A` on `ℕ →₀ A`. -/
private def stageAut (n : ℕ) : GL (Fin n) A →* ((ℕ →₀ A) ≃ₗ[Aᵐᵒᵖ] (ℕ →₀ A)) :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv Aᵐᵒᵖ (ℕ →₀ A)).toMonoidHom.comp
    (Units.map (cornerEnd n))

private theorem stageAut_apply_apply (n : ℕ) (u : GL (Fin n) A) (v : ℕ →₀ A) (i : ℕ) :
    stageAut n u v i = if h : i < n then ∑ j : Fin n, (u : Matrix (Fin n) (Fin n) A) ⟨i, h⟩ j * v j
      else v i := by
  simp [stageAut, LinearMap.GeneralLinearGroup.coeFn_generalLinearEquiv, cornerEnd_apply_apply]

private theorem stageAut_stabilizeGL {m n : ℕ} (h : m ≤ n) (u : GL (Fin m) A) :
    stageAut n (stabilizeGL A h u) = stageAut m u := by
  ext v i
  rw [stageAut_apply_apply, stageAut_apply_apply]
  simp only [coe_stabilizeGL_apply]
  by_cases him : i < m
  · rw [dite_eq_left (him.trans_le h), dite_eq_left him]
    -- Only the first `m` columns of `u ⊕ 1` meet row `i`.
    refine (Fintype.sum_of_injective (Fin.castLE h) (Fin.castLE_injective h) _ _ (fun j hj ↦ ?_)
      fun j ↦ ?_).symm
    · have hjm : ¬ (j : ℕ) < m := fun hjm ↦ hj ⟨⟨j, hjm⟩, rfl⟩
      rw [dite_eq_right fun h' ↦ hjm h'.2, Matrix.one_apply_ne fun hij ↦ hjm (by
        rw [← hij]; exact him), zero_mul]
    · rw [dite_eq_left ⟨him, j.isLt⟩]
      simp
  · rw [dite_eq_right him]
    split_ifs with hin
    · rw [Fintype.sum_eq_single ⟨i, hin⟩ fun j hj ↦ by
        rw [dite_eq_right fun h' ↦ him h'.1, Matrix.one_apply_ne (Ne.symm hj), zero_mul]]
      rw [dite_eq_right fun h' ↦ him h'.1, Matrix.one_apply_eq, one_mul]
    · rfl

end Action

/-! ## The action of `GL_∞(A)` and its image -/

namespace StableGeneralLinearGroup

variable {A}

variable (A) in
/-- The action of `GL_∞(A)` on the free right `A`-module `ℕ →₀ A`: an invertible matrix
`u : GL (Fin n) A` acts by `u` on the first `n` coordinates of a column vector and by the identity
on the others, so that column `j` of `u` is the image of the basis vector `eⱼ`. -/
def toFreeModuleAut : StableGeneralLinearGroup A →* ((ℕ →₀ A) ≃ₗ[Aᵐᵒᵖ] (ℕ →₀ A)) :=
  lift stageAut fun _ _ h u ↦ stageAut_stabilizeGL h u

/-- The coordinates of the image of a vector under an invertible matrix `u : GL (Fin n) A`: the
first `n` are those of `u` times the vector, the others are unchanged. -/
theorem toFreeModuleAut_of_apply_apply {n : ℕ} (u : GL (Fin n) A) (v : ℕ →₀ A) (i : ℕ) :
    toFreeModuleAut A (of A n u) v i =
      if h : i < n then ∑ j : Fin n, (u : Matrix (Fin n) (Fin n) A) ⟨i, h⟩ j * v j else v i := by
  rw [toFreeModuleAut, lift_of, stageAut_apply_apply]

/-- An invertible matrix `u : GL (Fin n) A` sends `eₖ a` to column `k` of `u` times `a` when
`k < n`, and fixes it otherwise. -/
@[simp]
theorem toFreeModuleAut_of_apply_single {n : ℕ} (u : GL (Fin n) A) (k : ℕ) (a : A) :
    toFreeModuleAut A (of A n u) (single k a) =
      if h : k < n then ∑ i : Fin n, single (i : ℕ) ((u : Matrix (Fin n) (Fin n) A) i ⟨k, h⟩ * a)
      else single k a := by
  ext i
  rw [toFreeModuleAut_of_apply_apply]
  split_ifs with hi hk hk
  · rw [sum_mul_single_apply, dite_eq_left hk, ← coordinateInclusion_eq_sum (R := Aᵐᵒᵖ),
      coordinateInclusion_apply, dite_eq_left hi]
  · rw [sum_mul_single_apply, dite_eq_right hk, single_eq_of_ne (by omega)]
  · rw [← coordinateInclusion_eq_sum (R := Aᵐᵒᵖ), coordinateInclusion_apply, dite_eq_right hi,
      single_eq_of_ne (by omega)]
  · rfl

/-- The elementary matrix `e_{ij}(a)` sends `eⱼ b` to `eⱼ b + eᵢ (a b)` and fixes every other
`eₖ b`. -/
theorem toFreeModuleAut_stableTransvection_apply_single {i j : ℕ} (hij : i ≠ j) (a : A) (k : ℕ)
    (b : A) :
    toFreeModuleAut A (stableTransvection ⟨(i, j), hij⟩ a) (single k b) =
      if k = j then single j b + single i (a * b) else single k b := by
  rw [stableTransvection_eq_of ⟨(i, j), hij⟩ a (n := max i j + 1) (by dsimp; omega)
    (by dsimp; omega)]
  ext l
  simp only [toFreeModuleAut_of_apply_apply, sum_mul_single_apply,
    coe_transvectionUnit_eq_one_add_single, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply,
    Fin.ext_iff]
  split_ifs <;> subst_vars <;> simp_all [Finsupp.single_apply] <;> omega

/-- The action of `GL_∞(A)` on `ℕ →₀ A` is faithful. -/
theorem toFreeModuleAut_injective : Function.Injective (toFreeModuleAut A) := by
  refine (injective_iff_map_eq_one _).2 fun x hx ↦ ?_
  obtain ⟨n, u, rfl⟩ := exists_of x
  suffices u = 1 by rw [this, map_one]
  ext i j
  have := congr($hx (single (j : ℕ) 1) i)
  rw [toFreeModuleAut_of_apply_apply, dite_eq_left i.isLt, sum_mul_single_apply,
    dite_eq_left j.isLt, mul_one] at this
  simpa [Matrix.one_apply, Finsupp.single_apply, Fin.ext_iff, eq_comm] using this

/-- An automorphism fixing `eₖ` for `k ≥ n` and preserving the first `n` coordinates is the image
of the invertible matrix of its values on `e₀, …, e_{n-1}`. -/
private theorem exists_toFreeModuleAut_of_eq {g : (ℕ →₀ A) ≃ₗ[Aᵐᵒᵖ] (ℕ →₀ A)} {n : ℕ}
    (hg : IsFinitaryOn (g : (ℕ →₀ A) →ₗ[Aᵐᵒᵖ] (ℕ →₀ A)) (Finset.range n)) :
    ∃ u : GL (Fin n) A, toFreeModuleAut A (of A n u) = g := by
  have hmem {k : ℕ} (hk : k < n) : k ∈ (Finset.range n : Set ℕ) := by simpa using hk
  -- The truncated matrices of `g` and `g⁻¹` are mutually inverse.
  obtain ⟨u, hu⟩ : ∃ u : GL (Fin n) A, (u : Matrix (Fin n) (Fin n) A) = coordMatrix g n :=
    ⟨⟨coordMatrix g n, coordMatrix g.symm n,
      by rw [coordMatrix_mul _ hg.symm.2, LinearEquiv.comp_symm, coordMatrix_id],
      by rw [coordMatrix_mul _ hg.2, LinearEquiv.symm_comp, coordMatrix_id]⟩, rfl⟩
  refine ⟨u, LinearEquiv.toLinearMap_injective (Finsupp.lhom_ext fun k a ↦ ?_)⟩
  rw [LinearEquiv.coe_coe, toFreeModuleAut_of_apply_single, hu]
  split_ifs with hk
  · have hgk := hg.map_mem_supported (single_mem_supported Aᵐᵒᵖ a (hmem hk))
    rw [← coordinateInclusion_coordinateRestriction hgk, coordinateInclusion_eq_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [coordinateRestriction_apply, map_single_eq_op_smul, Finsupp.smul_apply, op_smul_eq_mul,
      coordMatrix, Matrix.of_apply]
  · rw [map_single_eq_op_smul, hg.1 k (by simpa using hk), op_smul_single_one]

/-- The image of `GL_∞(A)` in the automorphisms of `ℕ →₀ A` is the subgroup of finitary
automorphisms. -/
theorem range_toFreeModuleAut : (toFreeModuleAut A).range = finitaryAutomorphisms A := by
  ext g
  constructor
  · rintro ⟨x, rfl⟩
    obtain ⟨n, u, rfl⟩ := exists_of x
    refine mem_finitaryAutomorphisms_iff.2 ⟨Finset.range n, fun k hk ↦ ?_, fun k hk ↦ ?_⟩
    · rw [Finset.mem_range] at hk
      rw [toFreeModuleAut_of_apply_single, dite_eq_right hk]
    · rw [Finset.mem_range] at hk
      rw [toFreeModuleAut_of_apply_single, dite_eq_left hk]
      exact Submodule.sum_mem _ fun i _ ↦ single_mem_supported _ _ (by simp)
  · rw [mem_finitaryAutomorphisms_iff]
    rintro ⟨s, hs₁, hs₂⟩
    have hs : IsFinitaryOn (g : (ℕ →₀ A) →ₗ[Aᵐᵒᵖ] (ℕ →₀ A)) s := ⟨hs₁, hs₂⟩
    obtain ⟨n, hn⟩ := Finset.exists_nat_subset_range s
    obtain ⟨u, hu⟩ := exists_toFreeModuleAut_of_eq (hs.mono (Finset.coe_subset.2 hn))
    exact ⟨of A n u, hu⟩

variable (A) in
/-- **`GL_∞(A)` is the group of finitary automorphisms of the countable free module**: the action
of `GL_∞(A)` on `ℕ →₀ A` is an isomorphism onto `TauCeti.finitaryAutomorphisms A`. -/
def finitaryAutomorphismsEquiv : StableGeneralLinearGroup A ≃* finitaryAutomorphisms A :=
  (MonoidHom.ofInjective toFreeModuleAut_injective).trans
    (MulEquiv.subgroupCongr range_toFreeModuleAut)

/-- The isomorphism `TauCeti.StableGeneralLinearGroup.finitaryAutomorphismsEquiv A` is the action
`TauCeti.StableGeneralLinearGroup.toFreeModuleAut A`. -/
@[simp]
theorem coe_finitaryAutomorphismsEquiv_apply (x : StableGeneralLinearGroup A) :
    (finitaryAutomorphismsEquiv A x : (ℕ →₀ A) ≃ₗ[Aᵐᵒᵖ] (ℕ →₀ A)) = toFreeModuleAut A x := by
  simp [finitaryAutomorphismsEquiv, MonoidHom.ofInjective_apply]

end StableGeneralLinearGroup

end TauCeti
