/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.PathAlgebra.Basic
public import TauCeti.Algebra.Category.ModuleCat.Projective.Dimension
public import Mathlib.Algebra.Category.ModuleCat.ProjectiveDimension
public import Mathlib.LinearAlgebra.TensorProduct.Projective

/-!
# The standard resolution of a module over a path algebra

Let `A = kQ` be the path algebra of a quiver `Q` with finitely many vertices over a commutative
ring `k`, with vertex idempotents `eᵥ`. Every left `A`-module `M` has the **standard resolution**

```text
0 ⟶ ⨁_{b : i ⟶ j} A eⱼ ⊗_k eᵢ M ⟶ ⨁_v A eᵥ ⊗_k eᵥ M ⟶ M ⟶ 0,
x ⊗ m ↦ x b ⊗ m - x ⊗ b m   (from the component of `b`),
x ⊗ m ↦ x m,
```

a short exact sequence of `A`-modules. Its two left terms are projective when `M` is projective
over `k`, so over a field every `A`-module has projective dimension at most one, and all
`Extⁿ_A(M, N)` with `n ≥ 2` vanish: a path algebra over a field is hereditary. Neither acyclicity
of `Q` nor any finiteness of `M` is needed, and there may be infinitely many arrows; the one-loop
quiver, whose path algebra is the polynomial ring `k[X]`, is included.

Both left terms are realized inside the modules `A ⊗_k M` and `(Σ i j, i ⟶ j) →₀ A ⊗_k M`, as
ranges of `A`-linear idempotents. The vertex term is the range of `x ⊗ m ↦ ∑ᵥ x eᵥ ⊗ eᵥ m`
(`TauCeti.PathAlgebra.standardVertexTerm`), and the arrow term the range of `x ⊗ m ↦ x eⱼ ⊗ eᵢ m`
on the component of each arrow `b : i ⟶ j` (`TauCeti.PathAlgebra.standardArrowTerm`). As direct
summands of modules `A ⊗_k V` with `V` projective over `k`, both are projective.

Exactness is proved with a contracting homotopy of `k`-modules. For a path `q = bₙ ⋯ b₁` it
sends `q ⊗ m` to `∑ᵣ bₙ ⋯ bᵣ₊₁ ⊗ bᵣ₋₁ ⋯ b₁ m` in the component of `bᵣ`. The differential undoes
it up to the telescoping boundary `q ⊗ m - eₜ ⊗ q m`, and it undoes the differential exactly.

Mathematically, the sequence is the standard bimodule resolution of `A`
(`TauCeti.PathAlgebra.exact_arrowTensorDifferential_vertexTensorMul`) tensored over `A` with `M`.
It is written out directly, so that no tensor product over the noncommutative ring `A` is needed.

## Main definitions

* `TauCeti.PathAlgebra.standardVertexTerm`, `TauCeti.PathAlgebra.standardArrowTerm`: the terms
  `⨁_v A eᵥ ⊗_k eᵥ M` and `⨁_{b : i ⟶ j} A eⱼ ⊗_k eᵢ M`.
* `TauCeti.PathAlgebra.standardDifferential`: the map `x ⊗ m ↦ x b ⊗ m - x ⊗ b m` between them.
* `TauCeti.PathAlgebra.standardAugmentation`: the action map `x ⊗ m ↦ x m` onto `M`.

## Main results

* `TauCeti.PathAlgebra.standardDifferential_injective`,
  `TauCeti.PathAlgebra.exact_standardDifferential_standardAugmentation` and
  `TauCeti.PathAlgebra.standardAugmentation_surjective`: **the standard resolution is a short
  exact sequence**, with projective terms by the instances on `standardVertexTerm` and
  `standardArrowTerm`.
* `TauCeti.hasProjectiveDimensionLT_two_pathAlgebra`: **path algebras are hereditary**: every
  module over the path algebra over a field of a quiver with finitely many vertices has
  projective dimension at most one.
* `TauCeti.subsingleton_ext_pathAlgebra`: `Extⁿ(M, N) = 0` for `n ≥ 2`.

## References

* W. Crawley-Boevey, *Lectures on representations of quivers*, Section 1, the standard
  resolution and its consequence (1).
* I. Assem, D. Simson, A. Skowroński, *Elements of the Representation Theory of Associative
  Algebras I*, Section VII.1, for the finite acyclic case.
-/

public section

universe u v w t

namespace TauCeti

namespace PathAlgebra

open TensorProduct
open scoped TensorProduct

section Resolution

variable (k : Type w) [CommRing k] (Q : Type u) [Quiver.{v} Q] [Fintype Q]
  (M : Type t) [AddCommGroup M] [Module (pathAlgebra k Q) M] [Module k M]
  [IsScalarTower k (pathAlgebra k Q) M]

/-- The path algebra, in this file. -/
local notation "𝒜" => pathAlgebra k Q

/-- The vertex idempotent `eᵥ`, in this file. -/
local notation "ε" => vertexIdempotent k

/-- The finitely supported families of elements of `kQ ⊗_k M` indexed by the arrows, in this
file. -/
local notation "𝓕" => (Σ i j : Q, i ⟶ j) →₀ TensorProduct k (pathAlgebra k Q) M

section Terms

/-! ### The vertex term -/

/-- The `kQ`-linear idempotent `x ⊗ m ↦ ∑ᵥ x eᵥ ⊗ eᵥ m` of `kQ ⊗_k M`, whose range is the
vertex term `⨁_v kQ eᵥ ⊗_k eᵥ M` of the standard resolution. -/
noncomputable def vertexProjection : 𝒜 ⊗[k] M →ₗ[𝒜] 𝒜 ⊗[k] M :=
  ∑ v : Q, AlgebraTensorModule.map (LinearMap.toSpanSingleton 𝒜 𝒜 (ε v))
    (Algebra.lsmul k k M (ε v))

variable {k Q M}

/-- The vertex projection on a pure tensor. -/
@[simp]
theorem vertexProjection_tmul (x : 𝒜) (m : M) :
    vertexProjection k Q M (x ⊗ₜ m) = ∑ v : Q, (x * ε v) ⊗ₜ[k] (ε v • m) := by
  simp [vertexProjection]

/-- The vertex projection is idempotent. -/
@[simp]
theorem vertexProjection_vertexProjection (z : 𝒜 ⊗[k] M) :
    vertexProjection k Q M (vertexProjection k Q M z) = vertexProjection k Q M z := by
  induction z using TensorProduct.inductionOn with
  | add z z' hz hz' => rw [map_add, map_add, hz, hz']
  | tmul x m =>
    rw [vertexProjection_tmul, map_sum]
    refine Finset.sum_congr rfl fun v _ ↦ ?_
    rw [vertexProjection_tmul, Finset.sum_eq_single v (fun w _ hw ↦ ?_) (by simp),
      mul_assoc, vertexIdempotent_mul_self, smul_smul, vertexIdempotent_mul_self]
    rw [mul_assoc, vertexIdempotent_mul_vertexIdempotent_of_ne (Ne.symm hw), mul_zero,
      zero_tmul]

variable (k Q M)

/-- The vertex term `⨁_v kQ eᵥ ⊗_k eᵥ M` of the standard resolution, the range of the vertex
projection on `kQ ⊗_k M`. -/
noncomputable def standardVertexTerm : Submodule 𝒜 (𝒜 ⊗[k] M) :=
  LinearMap.range (vertexProjection k Q M)

variable {k Q M}

/-- An element lies in the vertex term exactly when the vertex projection fixes it. -/
theorem mem_standardVertexTerm_iff {z : 𝒜 ⊗[k] M} :
    z ∈ standardVertexTerm k Q M ↔ vertexProjection k Q M z = z := by
  refine ⟨?_, fun h ↦ ⟨z, h⟩⟩
  rintro ⟨z, rfl⟩
  exact vertexProjection_vertexProjection z

/-- The vertex projection takes values in the vertex term. -/
theorem vertexProjection_mem_standardVertexTerm (z : 𝒜 ⊗[k] M) :
    vertexProjection k Q M z ∈ standardVertexTerm k Q M :=
  ⟨z, rfl⟩

/-- The vertex term is projective when `M` is projective over `k`, as a direct summand of
`kQ ⊗_k M`. -/
instance [Module.Projective k M] : Module.Projective 𝒜 (standardVertexTerm k Q M) :=
  Module.Projective.of_split (standardVertexTerm k Q M).subtype
    (vertexProjection k Q M).rangeRestrict <| LinearMap.ext fun z ↦ Subtype.ext <|
      mem_standardVertexTerm_iff.1 z.property

/-! ### The arrow term -/

variable (k Q M)

/-- The `kQ`-linear idempotent of the finitely supported families `(Σ i j, i ⟶ j) →₀ kQ ⊗_k M`
acting by `x ⊗ m ↦ x eⱼ ⊗ eᵢ m` on the component of each arrow `b : i ⟶ j`. Its range is the
arrow term `⨁_{b : i ⟶ j} kQ eⱼ ⊗_k eᵢ M` of the standard resolution. -/
noncomputable def arrowProjection : (𝓕) →ₗ[𝒜] 𝓕 :=
  Finsupp.lsum ℕ fun b ↦ Finsupp.lsingle b ∘ₗ
    AlgebraTensorModule.map (LinearMap.toSpanSingleton 𝒜 𝒜 (ε b.2.1))
      (Algebra.lsmul k k M (ε b.1))

variable {k Q M}

/-- The arrow projection on a pure tensor in the component of one arrow. -/
@[simp]
theorem arrowProjection_single_tmul (b : Σ i j : Q, i ⟶ j) (x : 𝒜) (m : M) :
    arrowProjection k Q M (Finsupp.single b (x ⊗ₜ m)) =
      Finsupp.single b ((x * ε b.2.1) ⊗ₜ[k] (ε b.1 • m)) := by
  simp [arrowProjection]

/-- The arrow projection is idempotent. -/
@[simp]
theorem arrowProjection_arrowProjection (y : 𝓕) :
    arrowProjection k Q M (arrowProjection k Q M y) = arrowProjection k Q M y := by
  induction y using Finsupp.induction_linear with
  | zero => simp
  | add y y' hy hy' => rw [map_add, map_add, hy, hy']
  | single b z =>
    induction z using TensorProduct.inductionOn with
    | add z z' hz hz' => rw [Finsupp.single_add, map_add, map_add, hz, hz']
    | tmul x m =>
      rw [arrowProjection_single_tmul, arrowProjection_single_tmul, mul_assoc,
        vertexIdempotent_mul_self, smul_smul, vertexIdempotent_mul_self]

variable (k Q M)

/-- The arrow term `⨁_{b : i ⟶ j} kQ eⱼ ⊗_k eᵢ M` of the standard resolution, the range of the
arrow projection. -/
noncomputable def standardArrowTerm : Submodule 𝒜 (𝓕) :=
  LinearMap.range (arrowProjection k Q M)

variable {k Q M}

/-- An element lies in the arrow term exactly when the arrow projection fixes it. -/
theorem mem_standardArrowTerm_iff {y : 𝓕} :
    y ∈ standardArrowTerm k Q M ↔ arrowProjection k Q M y = y := by
  refine ⟨?_, fun h ↦ ⟨y, h⟩⟩
  rintro ⟨y, rfl⟩
  exact arrowProjection_arrowProjection y

/-- The arrow projection takes values in the arrow term. -/
theorem arrowProjection_mem_standardArrowTerm (y : 𝓕) :
    arrowProjection k Q M y ∈ standardArrowTerm k Q M :=
  ⟨y, rfl⟩

/-- The arrow term is projective when `M` is projective over `k`, as a direct summand of
`(Σ i j, i ⟶ j) →₀ kQ ⊗_k M`. -/
instance [Module.Projective k M] : Module.Projective 𝒜 (standardArrowTerm k Q M) :=
  Module.Projective.of_split (standardArrowTerm k Q M).subtype
    (arrowProjection k Q M).rangeRestrict <| LinearMap.ext fun y ↦ Subtype.ext <|
      mem_standardArrowTerm_iff.1 y.property

end Terms

/-! ### The differential and the augmentation on the ambient modules -/

section Ambient

/-- The differential `x ⊗ m ↦ x b ⊗ m - x ⊗ b m` on the component of each arrow `b`, defined on
all of `(Σ i j, i ⟶ j) →₀ kQ ⊗_k M`. -/
noncomputable def arrowDifferential : (𝓕) →ₗ[𝒜] 𝒜 ⊗[k] M :=
  Finsupp.lsum ℕ fun b ↦
    AlgebraTensorModule.map (LinearMap.toSpanSingleton 𝒜 𝒜 (ofArrow b.2.2 : 𝒜)) LinearMap.id -
      AlgebraTensorModule.map LinearMap.id (Algebra.lsmul k k M (ofArrow b.2.2 : 𝒜))

/-- The action map `x ⊗ m ↦ x m` on all of `kQ ⊗_k M`. -/
noncomputable def tensorAction : 𝒜 ⊗[k] M →ₗ[𝒜] M :=
  AlgebraTensorModule.lift (LinearMap.toSpanSingleton 𝒜 (M →ₗ[k] M) LinearMap.id)

variable {k Q M}

/-- The differential on a pure tensor in the component of one arrow. -/
@[simp]
theorem arrowDifferential_single_tmul (b : Σ i j : Q, i ⟶ j) (x : 𝒜) (m : M) :
    arrowDifferential k Q M (Finsupp.single b (x ⊗ₜ m)) =
      (x * ofArrow b.2.2) ⊗ₜ[k] m - x ⊗ₜ[k] ((ofArrow b.2.2 : 𝒜) • m) := by
  simp [arrowDifferential]

/-- The action map on a pure tensor. -/
@[simp]
theorem tensorAction_tmul (x : 𝒜) (m : M) : tensorAction k Q M (x ⊗ₜ m) = x • m := by
  simp [tensorAction]

end Ambient

/-! ### The contracting homotopy -/

section Homotopy

variable {k Q M}

/-- The contracting homotopy on `q ⊗ m`, for a path `q`: the sum, over the factorizations
`q = q'' c q'` with `c` an arrow, of `q'' ⊗ q' m` in the component of `c`. It is defined by
recursion on the last arrow of `q`. -/
private noncomputable def homotopyPath : {s t : Q} → Quiver.Path s t → M →ₗ[k] 𝓕
  | _, _, .nil => 0
  | _, t, .cons q c => Algebra.lsmul k k 𝓕 (ofArrow c : 𝒜) ∘ₗ homotopyPath q +
      Finsupp.lsingle ⟨_, _, c⟩ ∘ₗ TensorProduct.mk k 𝒜 M (ε t) ∘ₗ
        Algebra.lsmul k k M (ofPath ⟨_, _, q⟩ : 𝒜)

private theorem homotopyPath_nil (s : Q) (m : M) :
    homotopyPath (k := k) (Quiver.Path.nil : Quiver.Path s s) m = 0 := by
  simp [homotopyPath]

private theorem homotopyPath_cons {s t t' : Q} (q : Quiver.Path s t) (c : t ⟶ t') (m : M) :
    homotopyPath (q.cons c) m = (ofArrow c : 𝒜) • homotopyPath q m +
      Finsupp.single ⟨t, t', c⟩ (ε t' ⊗ₜ[k] ((ofPath ⟨s, t, q⟩ : 𝒜) • m)) := by
  simp [homotopyPath]

/-- The homotopy on `q ⊗ m` only sees the component `eₛ m` at the source `s` of `q`. -/
private theorem homotopyPath_vertexIdempotent_smul {s t : Q} (q : Quiver.Path s t) (m : M) :
    homotopyPath q (ε s • m) = homotopyPath (k := k) q m := by
  induction q with
  | nil => rw [homotopyPath_nil, homotopyPath_nil]
  | cons q c ih =>
    rw [homotopyPath_cons, homotopyPath_cons, ih, smul_smul, ofPath_mul_vertexIdempotent]

/-- The homotopy on a path whose first arrow is `c : i ⟶ j` splits off the term of `c`. -/
private theorem homotopyPath_toPath_comp {i j t : Q} (c : i ⟶ j) (q : Quiver.Path j t) (m : M) :
    homotopyPath (c.toPath.comp q) m = homotopyPath q ((ofArrow c : 𝒜) • m) +
      Finsupp.single ⟨i, j, c⟩ ((ofPath ⟨j, t, q⟩ : 𝒜) ⊗ₜ[k] (ε i • m)) := by
  induction q with
  | nil =>
    rw [Quiver.Path.comp_nil, Quiver.Hom.toPath, homotopyPath_cons, homotopyPath_nil,
      homotopyPath_nil, smul_zero, zero_add, zero_add, ← vertexIdempotent_eq_ofPath,
      ← vertexIdempotent_eq_ofPath]
  | @cons t t' q d ih =>
    rw [Quiver.Path.comp_cons, homotopyPath_cons, ih, homotopyPath_cons, smul_add,
      Finsupp.smul_single, smul_tmul', smul_eq_mul, ofArrow_mul_ofPath, smul_smul,
      ofArrow_eq_ofPath c, ofPath_mul_ofPath_of_comp]
    abel

/-- The contracting homotopy `kQ ⊗_k M → (Σ i j, i ⟶ j) →₀ kQ ⊗_k M` of `k`-modules, sending
`q ⊗ m`, for a path `q`, to `homotopyPath q m`. -/
private noncomputable def homotopy : 𝒜 ⊗[k] M →ₗ[k] 𝓕 :=
  TensorProduct.lift
    (liftLinear k fun q : Quiver.TotalPath Q ↦ homotopyPath (k := k) (M := M) q.2.2)

private theorem homotopy_ofPath_tmul {s t : Q} (q : Quiver.Path s t) (m : M) :
    homotopy ((ofPath ⟨s, t, q⟩ : 𝒜) ⊗ₜ[k] m) = homotopyPath q m := by
  simp [homotopy]

/-- The boundary of the homotopy on `q ⊗ m` telescopes to `q ⊗ eₛ m - eₜ ⊗ q m`. -/
private theorem arrowDifferential_homotopyPath {s t : Q} (q : Quiver.Path s t) (m : M) :
    arrowDifferential k Q M (homotopyPath q m) =
      (ofPath ⟨s, t, q⟩ : 𝒜) ⊗ₜ[k] (ε s • m) - ε t ⊗ₜ[k] ((ofPath ⟨s, t, q⟩ : 𝒜) • m) := by
  induction q with
  | nil => rw [homotopyPath_nil, map_zero, ← vertexIdempotent_eq_ofPath, sub_self]
  | @cons t t' q c ih =>
    rw [homotopyPath_cons, map_add, map_smul, ih, arrowDifferential_single_tmul, smul_sub,
      smul_tmul', smul_tmul', smul_eq_mul, smul_eq_mul, ofArrow_mul_ofPath,
      ofArrow_mul_vertexIdempotent_self, vertexIdempotent_mul_ofArrow_self, smul_smul,
      ofArrow_mul_ofPath]
    abel

/-- The vertex projection of `q ⊗ m`, for a path `q` from `s`, is `q ⊗ eₛ m`. -/
private theorem vertexProjection_ofPath_tmul {s t : Q} (q : Quiver.Path s t) (m : M) :
    vertexProjection k Q M ((ofPath ⟨s, t, q⟩ : 𝒜) ⊗ₜ[k] m) =
      (ofPath ⟨s, t, q⟩ : 𝒜) ⊗ₜ[k] (ε s • m) := by
  rw [vertexProjection_tmul, Finset.sum_eq_single s (fun v _ hv ↦ ?_) (by simp),
    ofPath_mul_vertexIdempotent]
  rw [ofPath_mul_vertexIdempotent_of_ne _ hv, zero_tmul]

/-- The vertex projection of `1 ⊗ q m`, for a path `q` to `t`, is `eₜ ⊗ q m`. -/
private theorem vertexProjection_one_tmul_ofPath_smul {s t : Q} (q : Quiver.Path s t) (m : M) :
    vertexProjection k Q M ((1 : 𝒜) ⊗ₜ[k] ((ofPath ⟨s, t, q⟩ : 𝒜) • m)) =
      ε t ⊗ₜ[k] ((ofPath ⟨s, t, q⟩ : 𝒜) • m) := by
  rw [vertexProjection_tmul, Finset.sum_eq_single t (fun v _ hv ↦ ?_) (by simp), one_mul,
    smul_smul, vertexIdempotent_mul_ofPath]
  rw [smul_smul, vertexIdempotent_mul_ofPath_of_ne _ hv, zero_smul, tmul_zero]

/-- **The differential after the homotopy** is the identity on the vertex term, up to the
boundary term `π (1 ⊗ x m)` of the augmentation: `d (h z) = π z - π (1 ⊗ ε z)`. -/
private theorem arrowDifferential_homotopy (z : 𝒜 ⊗[k] M) :
    arrowDifferential k Q M (homotopy z) =
      vertexProjection k Q M z - vertexProjection k Q M (1 ⊗ₜ tensorAction k Q M z) := by
  -- Both sides are `k`-linear in `z`, so they agree as linear maps, compared on the `q ⊗ m`.
  have key : (arrowDifferential k Q M).restrictScalars k ∘ₗ homotopy =
      (vertexProjection k Q M).restrictScalars k - (vertexProjection k Q M).restrictScalars k ∘ₗ
        TensorProduct.mk k 𝒜 M 1 ∘ₗ (tensorAction k Q M).restrictScalars k := by
    refine TensorProduct.ext ((pathAlgebraBasis k Q).ext fun q ↦ LinearMap.ext fun m ↦ ?_)
    obtain ⟨s, t, q⟩ := q
    simp only [LinearMap.compr₂ₛₗ_apply, TensorProduct.mk_apply, coe_pathAlgebraBasis,
      LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.restrictScalars_apply,
      homotopy_ofPath_tmul, arrowDifferential_homotopyPath, tensorAction_tmul,
      vertexProjection_ofPath_tmul, vertexProjection_one_tmul_ofPath_smul]
  exact LinearMap.congr_fun key z

/-- **The homotopy after the differential** is the arrow projection: `h (d y) = π y`. -/
private theorem homotopy_arrowDifferential (y : 𝓕) :
    homotopy (arrowDifferential k Q M y) = arrowProjection k Q M y := by
  classical
  -- Both sides are `k`-linear in `y`, so they agree on the families `q ⊗ m` at one arrow.
  have key : homotopy ∘ₗ (arrowDifferential k Q M).restrictScalars k =
      (arrowProjection k Q M).restrictScalars k := by
    refine Finsupp.lhom_ext' fun b ↦ TensorProduct.ext
      ((pathAlgebraBasis k Q).ext fun q ↦ LinearMap.ext fun m ↦ ?_)
    obtain ⟨i, j, c⟩ := b
    obtain ⟨s, t, q⟩ := q
    simp only [LinearMap.compr₂ₛₗ_apply, TensorProduct.mk_apply, coe_pathAlgebraBasis,
      LinearMap.comp_apply, LinearMap.restrictScalars_apply, Finsupp.lsingle_apply,
      arrowDifferential_single_tmul, arrowProjection_single_tmul, map_sub,
      homotopy_ofPath_tmul]
    by_cases h : s = j
    · subst h
      rw [ofArrow_eq_ofPath, ofPath_mul_ofPath_of_comp, homotopy_ofPath_tmul,
        homotopyPath_toPath_comp, ofPath_mul_vertexIdempotent, ← ofArrow_eq_ofPath]
      abel
    · have hq : homotopyPath (k := k) q ((ofPath ⟨i, j, c.toPath⟩ : 𝒜) • m) = 0 := by
        rw [← homotopyPath_vertexIdempotent_smul, smul_smul, ← ofArrow_eq_ofPath,
          vertexIdempotent_mul_ofArrow]
        simp [Ne.symm h]
      rw [ofArrow_eq_ofPath, ofPath_mul_ofPath_of_not_composable (Ne.symm h),
        ofPath_mul_vertexIdempotent_of_ne _ (Ne.symm h), hq]
      simp
  exact LinearMap.congr_fun key y

end Homotopy

/-! ### Exactness -/

section Exactness

variable {k Q M}

/-- The augmentation vanishes on the image of the differential: `x b m - x (b m) = 0`. -/
private theorem tensorAction_arrowDifferential (y : 𝓕) :
    tensorAction k Q M (arrowDifferential k Q M y) = 0 := by
  induction y using Finsupp.induction_linear with
  | zero => simp
  | add y y' hy hy' => rw [map_add, map_add, hy, hy', add_zero]
  | single b z =>
    induction z using TensorProduct.inductionOn with
    | add z z' hz hz' => rw [Finsupp.single_add, map_add, map_add, hz, hz', add_zero]
    | tmul x m => simp [mul_smul]

/-- The augmentation is unchanged by the vertex projection, since `∑ᵥ eᵥ = 1`. -/
private theorem tensorAction_vertexProjection (z : 𝒜 ⊗[k] M) :
    tensorAction k Q M (vertexProjection k Q M z) = tensorAction k Q M z := by
  induction z using TensorProduct.inductionOn with
  | add z z' hz hz' => rw [map_add, map_add, map_add, hz, hz']
  | tmul x m =>
    simp only [vertexProjection_tmul, map_sum, tensorAction_tmul, smul_smul, mul_assoc,
      vertexIdempotent_mul_self]
    rw [← Finset.sum_smul, ← Finset.mul_sum, ← one_def, mul_one]

/-- The differential maps the arrow term into the vertex term. -/
private theorem arrowDifferential_mem_standardVertexTerm {y : 𝓕}
    (hy : y ∈ standardArrowTerm k Q M) :
    arrowDifferential k Q M y ∈ standardVertexTerm k Q M := by
  rw [mem_standardVertexTerm_iff]
  conv_rhs => rw [← mem_standardArrowTerm_iff.1 hy, ← homotopy_arrowDifferential,
    arrowDifferential_homotopy, tensorAction_arrowDifferential, tmul_zero, map_zero, sub_zero]

variable (k Q M)

/-- The differential `⨁_{b : i ⟶ j} kQ eⱼ ⊗_k eᵢ M → ⨁_v kQ eᵥ ⊗_k eᵥ M` of the standard
resolution, `x ⊗ m ↦ x b ⊗ m - x ⊗ b m` on the component of `b`. -/
noncomputable def standardDifferential : standardArrowTerm k Q M →ₗ[𝒜] standardVertexTerm k Q M :=
  ((arrowDifferential k Q M).domRestrict _).codRestrict _ fun y ↦
    arrowDifferential_mem_standardVertexTerm y.property

/-- The augmentation `⨁_v kQ eᵥ ⊗_k eᵥ M → M` of the standard resolution, `x ⊗ m ↦ x m`. -/
noncomputable def standardAugmentation : standardVertexTerm k Q M →ₗ[𝒜] M :=
  (tensorAction k Q M).domRestrict _

variable {k Q M}

/-- The differential of the standard resolution is the restriction of `arrowDifferential`. -/
@[simp]
theorem coe_standardDifferential (y : standardArrowTerm k Q M) :
    ((standardDifferential k Q M y : standardVertexTerm k Q M) : 𝒜 ⊗[k] M) =
      arrowDifferential k Q M y :=
  (rfl)

/-- The augmentation of the standard resolution is the restriction of `tensorAction`. -/
@[simp]
theorem standardAugmentation_apply (z : standardVertexTerm k Q M) :
    standardAugmentation k Q M z = tensorAction k Q M z :=
  (rfl)

/-- **The differential of the standard resolution is injective.** -/
theorem standardDifferential_injective : Function.Injective (standardDifferential k Q M) := by
  intro y y' h
  have h' : arrowDifferential k Q M y = arrowDifferential k Q M y' := congrArg Subtype.val h
  rw [Subtype.ext_iff, ← mem_standardArrowTerm_iff.1 y.property,
    ← mem_standardArrowTerm_iff.1 y'.property, ← homotopy_arrowDifferential,
    ← homotopy_arrowDifferential, h']

/-- **The standard resolution is exact in the middle**: the kernel of the augmentation is the
image of the differential. -/
theorem exact_standardDifferential_standardAugmentation :
    Function.Exact (standardDifferential k Q M) (standardAugmentation k Q M) := by
  intro z
  refine ⟨fun hz ↦ ?_, ?_⟩
  · -- The preimage is the projection of the homotopy of `z`.
    rw [standardAugmentation_apply] at hz
    have hd : arrowDifferential k Q M (homotopy (z : 𝒜 ⊗[k] M)) = z := by
      rw [arrowDifferential_homotopy, hz, tmul_zero, map_zero, sub_zero,
        mem_standardVertexTerm_iff.1 z.property]
    have key : arrowDifferential k Q M (arrowProjection k Q M (homotopy (z : 𝒜 ⊗[k] M))) = z := by
      rw [← homotopy_arrowDifferential, hd, hd]
    exact ⟨⟨_, arrowProjection_mem_standardArrowTerm (homotopy (z : 𝒜 ⊗[k] M))⟩,
      Subtype.ext key⟩
  · rintro ⟨y, rfl⟩
    exact tensorAction_arrowDifferential (y : 𝓕)

/-- **The augmentation of the standard resolution is surjective**: `m` is the image of
`∑ᵥ eᵥ ⊗ eᵥ m`. -/
theorem standardAugmentation_surjective : Function.Surjective (standardAugmentation k Q M) :=
  fun m ↦ ⟨⟨_, vertexProjection_mem_standardVertexTerm (1 ⊗ₜ m)⟩, by
    rw [standardAugmentation_apply, tensorAction_vertexProjection, tensorAction_tmul, one_smul]⟩

end Exactness

end Resolution

end PathAlgebra

open CategoryTheory

variable {k : Type w} [Field k] {Q : Type u} [Quiver.{v} Q] [Finite Q]

/-- Every module whose universe contains that of the path algebra has projective dimension at
most one: the kernel of the augmentation of its standard resolution is the image of the injective
differential, isomorphic to the projective arrow term. -/
private theorem hasProjectiveDimensionLT_two_of_isScalarTower (N : Type max u v w t)
    [AddCommGroup N] [Module (pathAlgebra k Q) N] [Module k N]
    [IsScalarTower k (pathAlgebra k Q) N] :
    HasProjectiveDimensionLT (ModuleCat.of (pathAlgebra k Q) N) 2 := by
  have := Fintype.ofFinite Q
  -- By dimension shifting along the augmentation, it suffices that its kernel is projective.
  refine (LinearMap.hasProjectiveDimensionLE_succ_iff_ker
    (P := PathAlgebra.standardVertexTerm k Q N) (M := N)
    PathAlgebra.standardAugmentation_surjective 0).2 ?_
  let K := LinearMap.ker (PathAlgebra.standardAugmentation k Q N)
  let e : K ≃ₗ[pathAlgebra k Q] PathAlgebra.standardArrowTerm k Q N :=
    (LinearEquiv.ofEq _ _
      PathAlgebra.exact_standardDifferential_standardAugmentation.linearMap_ker_eq).trans
      (LinearEquiv.ofInjective _ PathAlgebra.standardDifferential_injective).symm
  have : Module.Projective (pathAlgebra k Q) K := Module.Projective.of_equiv e.symm
  exact projective_iff_hasProjectiveDimensionLT_one.1 inferInstance

/-- **Path algebras are hereditary.** Every module over the path algebra of a quiver with finitely
many vertices, over a field, has projective dimension at most one. The quiver may have oriented
cycles and infinitely many arrows, and the module need not be finitely generated. -/
instance hasProjectiveDimensionLT_two_pathAlgebra [Small.{t} (pathAlgebra k Q)]
    (M : ModuleCat.{t} (pathAlgebra k Q)) : HasProjectiveDimensionLT M 2 := by
  -- Move `M` to a universe containing that of the path algebra, where the standard resolution
  -- lives, with the scalar action of `k` through the algebra map.
  let N := ULift.{max u v w} M
  let _ : Module k N := Module.compHom N (algebraMap k (pathAlgebra k Q))
  have : IsScalarTower k (pathAlgebra k Q) N := .of_algebraMap_smul fun _ _ ↦ rfl
  have := hasProjectiveDimensionLT_two_of_isScalarTower.{u, v, w, t} (k := k) (Q := Q) N
  exact ModuleCat.hasProjectiveDimensionLE_of_linearEquiv.{max u v w t, t}
    (M := ModuleCat.of (pathAlgebra k Q) N) (ULift.moduleEquiv (R := pathAlgebra k Q)) 1

/-- **Higher `Ext` vanishes over a path algebra**: for modules `M` and `N` over the path algebra
of a quiver with finitely many vertices over a field, `Extⁿ(M, N) = 0` for every `n ≥ 2`. -/
theorem subsingleton_ext_pathAlgebra [Small.{t} (pathAlgebra k Q)]
    (M N : ModuleCat.{t} (pathAlgebra k Q)) {n : ℕ} (hn : 2 ≤ n) :
    Subsingleton (Abelian.Ext M N n) :=
  HasProjectiveDimensionLT.subsingleton M 2 n hn N

end TauCeti
