/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Grassmannian.Basic
public import TauCeti.LinearAlgebra.ExteriorPower.BaseChange
public import TauCeti.LinearAlgebra.ExteriorPower.Basic
public import Mathlib.RingTheory.PicardGroup
import TauCeti.LinearAlgebra.ExteriorPower.Invertible

/-!
# The Plücker map on points of the Grassmannian

For a point `N` of the Grassmannian `G(k, X; R)` of quotients of `X` that are finite projective of
constant rank `k`, the top exterior power `⋀ᵏ (X ⧸ N)` is invertible, and the kernel of the
surjection `⋀ᵏ X → ⋀ᵏ (X ⧸ N)` is a point of `G(1, ⋀ᵏ X; R)`: the **Plücker point** of `N`
(`Module.Grassmannian.plucker`). Over an `R`-algebra `A`, with `X = A ⊗[R] M`, it is read in
`A ⊗[R] ⋀ᵏ M` through the base change isomorphism of exterior powers
(`Module.Grassmannian.pluckerBaseChange`), and it commutes with base change along `R`-algebra maps
(`Module.Grassmannian.pluckerBaseChange_map`). This naturality is what makes it the map on points of
the Plücker morphism of Grassmannian schemes (`Module.Grassmannian.pluckerHom`).

The naturality is proved through the observation that two points of `G(k, X; R)` one of which
contains the other are equal (`Module.Grassmannian.eq_of_le`): the induced surjection between the
quotients splits, and its kernel is finite projective of rank zero.

## Main definitions

* `Module.Grassmannian.plucker`: the Plücker point `ker (⋀ᵏ X → ⋀ᵏ (X ⧸ N))` of `N`.
* `Module.Grassmannian.pluckerBaseChange`: the Plücker point of `N ∈ G(k, A ⊗[R] M; A)`, as a point
  of `G(1, A ⊗[R] ⋀ᵏ M; A)`.

## Main results

* `Module.Grassmannian.eq_of_le`: comparable points of a Grassmannian are equal.
* `Module.Grassmannian.toSubmodule_plucker_ofSurjective`: the Plücker point of the kernel of
  `φ : X ↠ P` is the kernel of `⋀ᵏ φ`.
* `Module.Grassmannian.pluckerBaseChange_map`: naturality in the algebra.
* `Module.Grassmannian.exteriorPower_map_two_mulVecLin`: the Plücker coordinates
  `(1 : c : d : -a : -b : ad - bc)` of the chart point `((1, 0, a, b), (0, 1, c, d))` of
  `G(2, A⁴)`, and the Plücker relation they satisfy.
-/

public section

universe u v w

open TensorProduct

namespace Module.Grassmannian

section EqOfLE

variable {R : Type u} [CommRing R] {X : Type v} [AddCommGroup X] [Module R X] {k : ℕ}

/-- **Points of a Grassmannian are incomparable unless equal.** If `N₁ ≤ N₂` are points of
`G(k, X; R)`, the induced surjection `X ⧸ N₁ → X ⧸ N₂` of finite projective modules of the same
constant rank `k` is injective, so `N₁ = N₂`. -/
theorem eq_of_le {N₁ N₂ : G(k, X; R)} (h : N₁.toSubmodule ≤ N₂.toSubmodule) : N₁ = N₂ := by
  ext1
  refine le_antisymm h fun x hx ↦ ?_
  set π := Submodule.factor h
  obtain ⟨s, hs⟩ := Module.projective_lifting_property π LinearMap.id
    (Submodule.factor_surjective h)
  have hs' : ∀ z, π (s z) = z := fun z ↦ LinearMap.congr_fun hs z
  -- the kernel of `π` is a direct summand, of rank zero
  set p : (X ⧸ N₁.toSubmodule) →ₗ[R] LinearMap.ker π :=
    LinearMap.codRestrict _ (LinearMap.id - s ∘ₗ π) fun y ↦ by
      simp [LinearMap.mem_ker, hs']
  have hp : ∀ y : LinearMap.ker π, p y = y := fun y ↦ Subtype.ext <| by
    simp [p, LinearMap.mem_ker.1 y.property]
  let e : (X ⧸ N₁.toSubmodule) ≃ₗ[R] (LinearMap.ker π × (X ⧸ N₂.toSubmodule)) :=
    { toLinearMap := p.prod π
      invFun := fun z ↦ z.1 + s z.2
      left_inv := fun y ↦ by simp [p]
      right_inv := fun z ↦ by
        ext
        · simp [p, LinearMap.mem_ker.1 z.1.property, hs']
        · simp [LinearMap.mem_ker.1 z.1.property, hs'] }
  have : Module.Finite R (LinearMap.ker π) :=
    Module.Finite.of_surjective p fun y ↦ ⟨y, hp y⟩
  have : Module.Projective R (LinearMap.ker π) :=
    Module.Projective.of_split (LinearMap.ker π).subtype p (LinearMap.ext hp)
  have hrank := rankAtStalk_prod (R := R) (LinearMap.ker π) (X ⧸ N₂.toSubmodule)
  rw [← rankAtStalk_eq_of_equiv e] at hrank
  have h0 : rankAtStalk (R := R) (LinearMap.ker π) = 0 := by
    ext q
    have := congr_fun hrank q
    simp only [Pi.add_apply, N₁.rankAtStalk_eq, N₂.rankAtStalk_eq] at this
    simp only [Pi.zero_apply]
    omega
  have hsub := rankAtStalk_eq_zero_iff_subsingleton.1 h0
  have hmem : N₁.toSubmodule.mkQ x ∈ LinearMap.ker π := by
    simpa [π, LinearMap.mem_ker] using hx
  have : (⟨_, hmem⟩ : LinearMap.ker π) = 0 := Subsingleton.elim _ _
  simpa using congr_arg Subtype.val this

end EqOfLE

section Plucker

variable {R : Type u} [CommRing R] {X : Type v} [AddCommGroup X] [Module R X] {k : ℕ}

/-- The top exterior power `⋀ᵏ (X ⧸ N)` of the quotient by a point `N` of `G(k, X; R)` is
invertible: finite projective of constant rank one. -/
theorem invertible_exteriorPower_quotient (N : G(k, X; R)) :
    Module.Invertible R (⋀[R]^k (X ⧸ N.toSubmodule)) :=
  exteriorPower.invertible_of_rankAtStalk_eq N.rankAtStalk_eq

/-- **The Plücker point** of `N ∈ G(k, X; R)`: the kernel of the surjection
`⋀ᵏ X → ⋀ᵏ (X ⧸ N)` onto an invertible module, a point of `G(1, ⋀ᵏ X; R)`. -/
noncomputable def plucker (N : G(k, X; R)) : G(1, ⋀[R]^k X; R) :=
  have := invertible_exteriorPower_quotient N
  ofSurjective (exteriorPower.map k N.toSubmodule.mkQ)
    (exteriorPower.map_surjective N.toSubmodule.mkQ_surjective) fun p ↦ by
      rw [exteriorPower.rankAtStalk_eq_choose, N.rankAtStalk_eq, Nat.choose_self]

/-- The Plücker point of `N` is the kernel of `⋀ᵏ X → ⋀ᵏ (X ⧸ N)`. -/
@[simp]
theorem toSubmodule_plucker (N : G(k, X; R)) :
    (plucker N).toSubmodule = LinearMap.ker (exteriorPower.map k N.toSubmodule.mkQ) := by
  simp [plucker]

/-- The Plücker point of the kernel of a surjection `φ : X → P` onto a finite projective module of
constant rank `k` is the kernel of `⋀ᵏ φ`. -/
theorem toSubmodule_plucker_ofSurjective {P : Type*} [AddCommGroup P] [Module R P]
    [Module.Finite R P] [Module.Projective R P] (φ : X →ₗ[R] P) (hφ : Function.Surjective φ)
    (hP : ∀ p, rankAtStalk (R := R) P p = k) :
    (plucker (ofSurjective φ hφ hP)).toSubmodule = LinearMap.ker (exteriorPower.map k φ) := by
  set e := φ.quotKerEquivOfSurjective hφ
  have hφe : φ = e.toLinearMap ∘ₗ (LinearMap.ker φ).mkQ := by
    ext x
    simp [e]
  rw [toSubmodule_plucker, toSubmodule_ofSurjective]
  conv_rhs => rw [hφe, exteriorPower.map_comp, ← LinearEquiv.exteriorPower_toLinearMap,
    LinearMap.ker_comp, LinearEquiv.ker, Submodule.comap_bot]

end Plucker

section BaseChange

variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M] {k : ℕ}
  {A : Type w} [CommRing A] [Algebra R A] {B : Type w} [CommRing B] [Algebra R B]

/-- **The Plücker point over an `R`-algebra `A`.** The Plücker point of `N ∈ G(k, A ⊗[R] M; A)`,
read in `A ⊗[R] ⋀ᵏ M` through the base change isomorphism `⋀ᵏ_A (A ⊗[R] M) ≃ A ⊗[R] ⋀ᵏ M`. -/
noncomputable def pluckerBaseChange (N : G(k, A ⊗[R] M; A)) : G(1, A ⊗[R] ⋀[R]^k M; A) :=
  (TauCeti.exteriorPower.equivBaseChange A k).grassmannianCongr (plucker N)

/-- The Plücker point over `A` is the image of the kernel of
`⋀ᵏ_A (A ⊗[R] M) → ⋀ᵏ_A ((A ⊗[R] M) ⧸ N)` in `A ⊗[R] ⋀ᵏ M`. -/
theorem toSubmodule_pluckerBaseChange (N : G(k, A ⊗[R] M; A)) :
    (pluckerBaseChange N).toSubmodule =
      (LinearMap.ker (exteriorPower.map k N.toSubmodule.mkQ)).map
        (TauCeti.exteriorPower.equivBaseChange A k).toLinearMap := by
  simp [pluckerBaseChange]

/-- The `A`-span of the vectors `1 ⊗ m` is all of `A ⊗[R] M`. -/
private theorem span_one_tmul :
    Submodule.span A (Set.range fun m : M ↦ (1 : A) ⊗ₜ[R] m) = ⊤ := by
  refine Submodule.eq_top_iff'.2 fun x ↦ ?_
  induction x using TensorProduct.inductionOn with
  | tmul a m =>
    have : a ⊗ₜ[R] m = a • ((1 : A) ⊗ₜ[R] m) := by rw [smul_tmul', smul_eq_mul, mul_one]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨m, rfl⟩)
  | add x y hx hy => exact add_mem hx hy

/-- The value of `⋀ᵏ (B ⊗[R] M) → ⋀ᵏ ((B ⊗[R] M) ⧸ map f N)` on the image of
`(1 ⊗ m₁) ∧ ⋯ ∧ (1 ⊗ mₖ)` under `⋀ᵏ_A (A ⊗[R] M) ≃ A ⊗[R] ⋀ᵏ M → B ⊗[R] ⋀ᵏ M ≃ ⋀ᵏ_B (B ⊗[R] M)`. -/
private theorem map_mkQ_rTensor_ιMulti (f : A →ₐ[R] B) (N : G(k, A ⊗[R] M; A)) (m : Fin k → M) :
    exteriorPower.map k (map f N).toSubmodule.mkQ
      ((TauCeti.exteriorPower.equivBaseChange B k).symm
        (f.toLinearMap.rTensor (⋀[R]^k M) (TauCeti.exteriorPower.equivBaseChange A k
          (exteriorPower.ιMulti A k fun i ↦ (1 : A) ⊗ₜ[R] m i)))) =
      exteriorPower.ιMulti B k fun i ↦ (map f N).toSubmodule.mkQ ((1 : B) ⊗ₜ[R] m i) := by
  have hA := TauCeti.exteriorPower.equivBaseChange_ιMulti_tmul (R := R) A (fun _ ↦ (1 : A)) m
  simp only [Finset.prod_const_one] at hA
  rw [hA, LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply, map_one,
    TauCeti.exteriorPower.equivBaseChange_symm_tmul_ιMulti, one_smul,
    exteriorPower.map_apply_ιMulti]
  rfl

/-- The key step of `pluckerBaseChange_map`: the image under `f` of a vector of the Plücker point of
`N` lies in the Plücker point of `map f N`. -/
private theorem map_mkQ_rTensor_eq_zero (f : A →ₐ[R] B) (N : G(k, A ⊗[R] M; A))
    {x : ⋀[A]^k (A ⊗[R] M)} (hx : exteriorPower.map k N.toSubmodule.mkQ x = 0) :
    exteriorPower.map k (map f N).toSubmodule.mkQ
      ((TauCeti.exteriorPower.equivBaseChange B k).symm
        (f.toLinearMap.rTensor (⋀[R]^k M) (TauCeti.exteriorPower.equivBaseChange A k x))) = 0 := by
  algebraize [f.toRingHom]
  set Q := (B ⊗[R] M) ⧸ (map f N).toSubmodule
  -- the map `A ⊗[R] M → B ⊗[R] M` induced by `f`, as an `A`-linear map
  let h : A ⊗[R] M →ₗ[A] B ⊗[R] M := AlgebraTensorModule.rTensor R M (Algebra.linearMap A B)
  have hh : ∀ x, h x = f.toLinearMap.rTensor M x := fun x ↦ by
    induction x using TensorProduct.inductionOn with
    | tmul a m => rfl
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  let g : (A ⊗[R] M) ⧸ N.toSubmodule →ₗ[A] Q :=
    N.toSubmodule.mapQ ((map f N).toSubmodule.restrictScalars A) h fun x hx ↦ by
      simpa [hh] using rTensor_mem_map f hx
  -- the composite is `A`-linear and factors through `⋀ᵏ (A ⊗[R] M) → ⋀ᵏ ((A ⊗[R] M) ⧸ N)`
  let T : ⋀[A]^k (A ⊗[R] M) →ₗ[A] ⋀[B]^k Q :=
    ((exteriorPower.map k (map f N).toSubmodule.mkQ).restrictScalars A) ∘ₗ
      ((TauCeti.exteriorPower.equivBaseChange B k).symm.toLinearMap.restrictScalars A) ∘ₗ
      (AlgebraTensorModule.rTensor R (⋀[R]^k M) (Algebra.linearMap A B)) ∘ₗ
      (TauCeti.exteriorPower.equivBaseChange A k).toLinearMap
  let S : ⋀[A]^k ((A ⊗[R] M) ⧸ N.toSubmodule) →ₗ[A] ⋀[B]^k Q :=
    exteriorPower.alternatingMapLinearEquiv
      { toMultilinearMap :=
          ((exteriorPower.ιMulti B k).toMultilinearMap.restrictScalars A).compLinearMap
            fun _ ↦ g
        map_eq_zero_of_eq' := fun v i j hv hij ↦
          (exteriorPower.ιMulti B k).map_eq_zero_of_eq (fun l ↦ g (v l)) (by simp [hv]) hij }
  have hT (y) : T y = exteriorPower.map k (map f N).toSubmodule.mkQ
      ((TauCeti.exteriorPower.equivBaseChange B k).symm
        (f.toLinearMap.rTensor (⋀[R]^k M) (TauCeti.exteriorPower.equivBaseChange A k y))) := by
    simp only [T, LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_restrictScalars,
      LinearEquiv.coe_coe]
    congr 2
  have hTS : T = S ∘ₗ exteriorPower.map k N.toSubmodule.mkQ := by
    refine LinearMap.ext_on (exteriorPower.ιMulti_span_of_span A k (A ⊗[R] M) span_one_tmul)
      ?_
    rintro _ ⟨v, hv, rfl⟩
    choose m hm using fun i ↦ hv ⟨i, rfl⟩
    obtain rfl : v = fun i ↦ (1 : A) ⊗ₜ[R] m i := funext fun i ↦ (hm i).symm
    rw [hT, map_mkQ_rTensor_ιMulti, LinearMap.comp_apply, exteriorPower.map_apply_ιMulti,
      exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
    change _ = exteriorPower.ιMulti B k (fun i ↦ g (N.toSubmodule.mkQ (1 ⊗ₜ m i)))
    congr 1
    funext i
    change _ = (Submodule.Quotient.mk (h (1 ⊗ₜ m i)) : Q)
    simp [h]
  rw [← hT, hTS, LinearMap.comp_apply, hx, map_zero]

/-- **Naturality of the Plücker point.** For an `R`-algebra map `f : A → B`, the Plücker point of
the base change of `N` is the base change of the Plücker point of `N`. -/
theorem pluckerBaseChange_map (f : A →ₐ[R] B) (N : G(k, A ⊗[R] M; A)) :
    pluckerBaseChange (map f N) = map f (pluckerBaseChange N) := by
  refine (eq_of_le ?_).symm
  rw [map_toSubmodule_eq_span, Submodule.span_le]
  rintro _ ⟨y, hy, rfl⟩
  rw [toSubmodule_pluckerBaseChange] at hy
  obtain ⟨x, hx, rfl⟩ := hy
  rw [SetLike.mem_coe, toSubmodule_pluckerBaseChange, Submodule.mem_map_equiv, LinearMap.mem_ker]
  exact map_mkQ_rTensor_eq_zero f N hx

end BaseChange

section Check

variable {A : Type u} [CommRing A] {V : Type v} [AddCommGroup V] [Module A V]

/-- `(αu + βv) ∧ (γu + δv) = (αδ - βγ) u ∧ v`. -/
theorem ιMulti_two_add_smul (u v : V) (α β γ δ : A) :
    exteriorPower.ιMulti A 2 ![α • u + β • v, γ • u + δ • v] =
      (α * δ - β * γ) • exteriorPower.ιMulti A 2 ![u, v] := by
  apply Subtype.ext
  simp only [exteriorPower.ιMulti_apply_coe, ExteriorAlgebra.ιMulti_apply, List.ofFn_succ,
    List.ofFn_zero, Matrix.cons_val_zero, Matrix.cons_val_succ, List.prod_cons, List.prod_nil,
    mul_one, Submodule.coe_smul, map_add,
    map_smul, add_mul, mul_add, smul_mul_assoc, mul_smul_comm, ExteriorAlgebra.ι_sq_zero,
    smul_zero, zero_add, add_zero, Fin.isValue]
  have h : ExteriorAlgebra.ι A v * ExteriorAlgebra.ι A u =
      -(ExteriorAlgebra.ι A u * ExteriorAlgebra.ι A v) :=
    eq_neg_of_add_eq_zero_left (by rw [add_comm]; exact ExteriorAlgebra.ι_add_mul_swap u v)
  rw [h]
  module

/-- **The Plücker coordinates of a point of `G(2, A⁴)`.** The quotient `q : A⁴ → A²` with matrix
`((1, 0, a, b), (0, 1, c, d))`, the point of the chart indexed by the first two basis vectors,
has `⋀² q (eᵢ ∧ eⱼ) = pᵢⱼ f₁ ∧ f₂` with
`(p₁₂, p₁₃, p₁₄, p₂₃, p₂₄, p₃₄) = (1, c, d, -a, -b, ad - bc)`, and these satisfy the Plücker
relation `p₁₂ p₃₄ - p₁₃ p₂₄ + p₁₄ p₂₃ = 0`. By
`Module.Grassmannian.toSubmodule_plucker_ofSurjective`, the Plücker point of `ker q` is the kernel
of `⋀² q`, the linear form with these coordinates. Without the signs of the exterior power, the
coordinates `(1, c, d, a, b, ad - bc)` would give `2(ad - bc)` in the relation. -/
theorem exteriorPower_map_two_mulVecLin (a b c d : A) :
    let q := (!![1, 0, a, b; 0, 1, c, d] : Matrix (Fin 2) (Fin 4) A).mulVecLin
    let e : Fin 4 → Fin 4 → A := fun i ↦ Pi.single i 1
    let w := exteriorPower.ιMulti A 2 ![(Pi.single 0 1 : Fin 2 → A), Pi.single 1 1]
    exteriorPower.map 2 q (exteriorPower.ιMulti A 2 ![e 0, e 1]) = (1 : A) • w ∧
      exteriorPower.map 2 q (exteriorPower.ιMulti A 2 ![e 0, e 2]) = c • w ∧
      exteriorPower.map 2 q (exteriorPower.ιMulti A 2 ![e 0, e 3]) = d • w ∧
      exteriorPower.map 2 q (exteriorPower.ιMulti A 2 ![e 1, e 2]) = (-a) • w ∧
      exteriorPower.map 2 q (exteriorPower.ιMulti A 2 ![e 1, e 3]) = (-b) • w ∧
      exteriorPower.map 2 q (exteriorPower.ιMulti A 2 ![e 2, e 3]) = (a * d - b * c) • w ∧
      1 * (a * d - b * c) - c * (-b) + d * (-a) = 0 := by
  intro q e w
  have hcol : ∀ j : Fin 4, q (e j) =
      (!![1, 0, a, b; 0, 1, c, d] : Matrix (Fin 2) (Fin 4) A) 0 j • (Pi.single 0 1 : Fin 2 → A) +
        (!![1, 0, a, b; 0, 1, c, d] : Matrix (Fin 2) (Fin 4) A) 1 j • Pi.single 1 1 := by
    intro j
    ext i
    fin_cases i <;> simp [q, e, Matrix.mulVec, dotProduct, Pi.single_apply]
  have key : ∀ i j : Fin 4, exteriorPower.map 2 q (exteriorPower.ιMulti A 2 ![e i, e j]) =
      ((!![1, 0, a, b; 0, 1, c, d] : Matrix (Fin 2) (Fin 4) A) 0 i *
          (!![1, 0, a, b; 0, 1, c, d] : Matrix (Fin 2) (Fin 4) A) 1 j -
        (!![1, 0, a, b; 0, 1, c, d] : Matrix (Fin 2) (Fin 4) A) 1 i *
          (!![1, 0, a, b; 0, 1, c, d] : Matrix (Fin 2) (Fin 4) A) 0 j) • w := by
    intro i j
    rw [exteriorPower.map_apply_ιMulti]
    have : (q ∘ ![e i, e j]) = ![q (e i), q (e j)] := by
      ext l : 1
      fin_cases l <;> rfl
    rw [this, hcol, hcol, ιMulti_two_add_smul]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, by ring⟩ <;> rw [key] <;> simp
  ring_nf

end Check

end Module.Grassmannian
