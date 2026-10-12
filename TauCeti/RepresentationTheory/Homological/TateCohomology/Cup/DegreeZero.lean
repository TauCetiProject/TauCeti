/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.TateCohomology.Coinduced
public import TauCeti.RepresentationTheory.Homological.TateCohomology.Functoriality
public import TauCeti.RepresentationTheory.Homological.TateCohomology.Linear
public import TauCeti.RepresentationTheory.Rep.TensorInvariant

/-!
# The Tate cup product with a degree-zero class

For a finite group `G` and representations `M`, `N`, this file constructs the Tate cup product

`tateCohomology M n × tateCohomology N 0 → tateCohomology (M ⊗ N) n`

in every integer degree `n`. An invariant `y ∈ N^G` gives a morphism of representations
`M ⟶ M ⊗ N`, `m ↦ m ⊗ y`, and the cup product of `x ∈ tateCohomology M n` with the class of `y`
is the image of `x` under the induced map. The substance is that this depends only on the class of
`y` in `tateCohomology N 0 = N^G / N_G N`: when `y = N_G z` is a norm, `m ↦ m ⊗ N_G z` is the norm
`m ↦ ∑ g, g • (g⁻¹ • m ⊗ z)` of the linear map `m ↦ m ⊗ z`, so it factors through a coinduced
representation and induces zero on Tate cohomology.

This is the bidegree `(n, 0)` part of the cup product on Tate cohomology. It is compatible with the
connecting homomorphisms in the first variable, and the cup product of two degree-zero classes is
induced by `M^G ⊗ N^G → (M ⊗ N)^G`; these are the two properties from which the cup product in all
bidegrees is obtained by dimension shifting (Cassels–Fröhlich, Chapter IV, §7).

## Main definitions

* `TauCeti.TateCohomology.cupH0`: the cup product
  `tateCohomology M n × tateCohomology N 0 → tateCohomology (M ⊗ N) n`, as a `k`-bilinear map.

## Main statements

* `TauCeti.TateCohomology.map_tensorInvariant_eq_zero`: `m ↦ m ⊗ y` induces zero on Tate
  cohomology when `y` is a norm.
* `TauCeti.TateCohomology.cupH0_H0π`: the cup product with the class of an invariant `y` is the map
  induced by `m ↦ m ⊗ y`.
* `TauCeti.TateCohomology.cupH0_H0π_H0π`: in degree zero, the cup product of the classes of `x` and
  `y` is the class of `x ⊗ y`.
* `TauCeti.TateCohomology.cupH0_map_left`, `TauCeti.TateCohomology.cupH0_map_right`: naturality in
  both coefficient representations.
* `TauCeti.TateCohomology.δ_cupH0`: compatibility with the connecting homomorphism of a short exact
  sequence in the first variable which stays short exact after tensoring with `N`.

## References

* J. W. S. Cassels and A. Fröhlich (eds.), *Algebraic Number Theory*, Chapter IV (Atiyah–Wall),
  §6 and §7.
* K. S. Brown, *Cohomology of Groups*, Chapter VI, §5.
-/

public noncomputable section

universe u

open CategoryTheory Limits MonoidalCategory
open scoped TensorProduct

namespace TauCeti.TateCohomology

variable {k G : Type u} [CommRing k] [Group G] [Fintype G] {M N : Rep k G}

/-- If `y` is a norm, then `m ↦ m ⊗ y` induces zero on Tate cohomology in every degree: for
`y = N_G z` it is the norm `m ↦ ∑ g, g • (g⁻¹ • m ⊗ z)` of the linear map `m ↦ m ⊗ z`. -/
theorem map_tensorInvariant_eq_zero (M : Rep k G) {y : N.ρ.invariants}
    (hy : (y : N.V) ∈ LinearMap.range N.ρ.norm) (n : ℤ) :
    (tateCohomologyFunctor n).map (Rep.tensorInvariant M y) = 0 := by
  obtain ⟨z, hz⟩ := hy
  refine map_eq_zero_of_hom_apply_eq_sum _ ((TensorProduct.mk k M.V N.V).flip z) (fun m ↦ ?_) n
  simp [← hz, Representation.norm, Representation.tprod_apply, TensorProduct.tmul_sum,
    ← Module.End.mul_apply, ← map_mul]

variable (M N) in
/-- **The Tate cup product with a degree-zero class**,
`tateCohomology M n × tateCohomology N 0 → tateCohomology (M ⊗ N) n`: the cup product of `x` with
the class of an invariant `y` is the image of `x` under the map induced by `m ↦ m ⊗ y`
(`cupH0_H0π`). It is well defined because that map vanishes on Tate cohomology when
`y` is a norm (`map_tensorInvariant_eq_zero`). -/
def cupH0 (n : ℤ) :
    tateCohomology M n →ₗ[k] tateCohomology N 0 →ₗ[k] tateCohomology (M ⊗ N) n :=
  LinearMap.flip <|
    (((LinearMap.range N.ρ.norm).submoduleOf N.ρ.invariants).liftQ
      { toFun y := ((tateCohomologyFunctor n).map (Rep.tensorInvariant M y)).hom
        map_add' y z := by
          rw [Rep.tensorInvariant_add, Functor.map_add, ModuleCat.hom_add]
        map_smul' c y := by
          rw [Rep.tensorInvariant_smul, Functor.map_smul, ModuleCat.hom_smul, RingHom.id_apply] }
      fun y hy ↦ by
        rw [LinearMap.mem_ker, LinearMap.coe_mk, AddHom.coe_mk,
          map_tensorInvariant_eq_zero M hy n, ModuleCat.hom_zero]) ∘ₗ
      (H0IsoNormQuotient N).hom.hom

-- As for `H0π_eq_zero_iff`, `simp` reduces the carrier `ModuleCat.of k N.ρ.invariants` in the
-- implicit arguments of `H0π N y` before it looks a term up, so the left-hand side is stated
-- through `dsimp% only`.
/-- The cup product with the class of an invariant `y` is the map induced by `m ↦ m ⊗ y`. -/
@[simp]
theorem cupH0_H0π (n : ℤ) (x : tateCohomology M n) (y : N.ρ.invariants) :
    (dsimp% only (cupH0 M N n x (H0π N y))) =
      (tateCohomologyFunctor n).map (Rep.tensorInvariant M y) x := by
  simp only [cupH0, LinearMap.flip_apply, LinearMap.comp_apply,
    H0π_comp_H0IsoNormQuotient_hom_apply, Submodule.liftQ_apply,
    LinearMap.coe_mk, AddHom.coe_mk]

-- The left-hand side is stated through `dsimp% only` for the same reason as in `cupH0_H0π`. The
-- priority is `high` so that `simp` uses this lemma before the more general `cupH0_H0π`, which
-- would otherwise rewrite the left-hand side first.
/-- In degree zero, the cup product of the classes of invariants `x` and `y` is the class of the
invariant `x ⊗ y`. -/
@[simp high]
theorem cupH0_H0π_H0π (x : M.ρ.invariants) (y : N.ρ.invariants) :
    (dsimp% only (cupH0 M N 0 (H0π M x) (H0π N y))) =
      H0π (M ⊗ N) ⟨(x : M.V) ⊗ₜ[k] (y : N.V), fun g ↦ by
        simp [Representation.tprod_apply, x.2 g, y.2 g]⟩ := by
  rw [cupH0_H0π, H0π_comp_tateCohomologyFunctor_map_apply]
  congr 1
  apply Subtype.ext
  exact Rep.tensorInvariant_hom_apply M y x

/-- The cup product with a degree-zero class is natural in the first coefficient
representation. -/
theorem cupH0_map_left {M' : Rep k G} (f : M ⟶ M') (n : ℤ) (x : tateCohomology M n)
    (y : tateCohomology N 0) :
    cupH0 M' N n ((tateCohomologyFunctor n).map f x) y =
      (tateCohomologyFunctor n).map (f ▷ N) (cupH0 M N n x y) := by
  induction y using H0_induction_on with
  | h y =>
    rw [cupH0_H0π, cupH0_H0π, ← ModuleCat.comp_apply, ← ModuleCat.comp_apply, ← Functor.map_comp,
      ← Functor.map_comp, Rep.hom_comp_tensorInvariant]

/-- The cup product with a degree-zero class is natural in the second coefficient
representation. -/
theorem cupH0_map_right {N' : Rep k G} (g : N ⟶ N') (n : ℤ) (x : tateCohomology M n)
    (y : tateCohomology N 0) :
    cupH0 M N' n x ((tateCohomologyFunctor 0).map g y) =
      (tateCohomologyFunctor n).map (M ◁ g) (cupH0 M N n x y) := by
  induction y using H0_induction_on with
  | h y =>
    rw [← ModuleCat.comp_apply (H0π N), H0π_comp_tateCohomologyFunctor_map, ModuleCat.comp_apply,
      cupH0_H0π, cupH0_H0π, ← ModuleCat.comp_apply, ← Functor.map_comp,
      Rep.tensorInvariant_comp_whiskerLeft M g y ((Rep.invariantsFunctor k G).map g y) rfl]

/-- **The cup product with a degree-zero class commutes with the connecting homomorphism** in the
first variable: for a short exact sequence `0 → M₁ → M₂ → M₃ → 0` which stays short exact after
tensoring with `N` (for instance one that splits `k`-linearly), `δ (x ∪ y) = δ x ∪ y`. -/
theorem δ_cupH0 {S : ShortComplex (Rep k G)} (hS : S.ShortExact)
    (hSN : (S.map (tensorRight N)).ShortExact) (n : ℤ) (x : tateCohomology S.X₃ n)
    (y : tateCohomology N 0) :
    _root_.TateCohomology.δ hSN n (cupH0 S.X₃ N n x y) =
      cupH0 S.X₁ N (n + 1) (_root_.TateCohomology.δ hS n x) y := by
  induction y using H0_induction_on with
  | h y =>
    let F : S ⟶ S.map (tensorRight N) :=
      { τ₁ := Rep.tensorInvariant S.X₁ y
        τ₂ := Rep.tensorInvariant S.X₂ y
        τ₃ := Rep.tensorInvariant S.X₃ y
        comm₁₂ := by simpa using (Rep.hom_comp_tensorInvariant _ S.f y).symm
        comm₂₃ := by simpa using (Rep.hom_comp_tensorInvariant _ S.g y).symm }
    rw [cupH0_H0π, cupH0_H0π, ← ModuleCat.comp_apply, ← ModuleCat.comp_apply]
    exact congrArg (fun φ ↦ φ x) (_root_.TateCohomology.δ_naturality hS hSN F n).symm

end TauCeti.TateCohomology
