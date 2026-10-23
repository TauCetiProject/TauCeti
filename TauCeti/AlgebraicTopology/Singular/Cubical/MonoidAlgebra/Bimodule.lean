/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Cubical.MonoidAlgebra.Action
public import TauCeti.Algebra.Homology.DG.Bimodule.Defs

/-!
# Cubical chains on a space with commuting left and right monoid actions

Let `G` and `H` be topological monoids, with `G` acting continuously on a space `Y` from the left
and `H` from the right, and the two actions commuting.  The left action `G × Y → Y` and the cross
product of normalized cubical chains give a left action of the Pontryagin algebra of `G` on the
chains of `Y`: `a · c := act_* (a × c) : C^□_{p + q}(Y; R)` for `a ∈ C^□_p(G; R)` and
`c ∈ C^□_q(Y; R)`.  It is strictly associative and unital, the boundary is a derivation for it with
the Koszul sign `(-1) ^ p`, and it commutes strictly with the right action of the chains of `H` of
`TauCeti.AlgebraicTopology.Singular.Cubical.MonoidAlgebra.Action`.  Hence the module
`⨁ n, C^□_n(Y; R)` of that file is a **differential graded bimodule** over the DG algebras of
cubical chains of `G` and of `H`.

The basic example is the space of Moore paths from `b` to `b'`, on which the Moore loops at `b`
act by concatenation in front and those at `b'` by concatenation behind
(`TauCeti.MoorePathBetween`): its chains are the bimodule that changes the basepoint of a DG local
system.

## Main definitions

* `TauCeti.leftActMap G Y`: the left action `G × Y → Y`, `(g, y) ↦ g • y`.
* `TauCeti.NormalizedCubicalChain.leftAct G Y R p q`: the action
  `C^□_p(G; R) ⊗ C^□_q(Y; R) → C^□_{p + q}(Y; R)`.
* The `Module (normalizedCubicalChainAlgebra G R) (cubicalChainModule Y H R)` instance.

## Main results

* `TauCeti.NormalizedCubicalChain.leftAct_assoc`, `TauCeti.NormalizedCubicalChain.one_leftAct`:
  the left action is strictly associative and unital.
* `TauCeti.NormalizedCubicalChain.boundary_leftAct`: the Leibniz rule.
* `TauCeti.NormalizedCubicalChain.leftAct_act`: the left and right actions commute.
* `TauCeti.cubicalChainModule_isDGLeftModule`: the chains form a DG left module.
* `TauCeti.cubicalChainModule_isDGBimodule`: with commuting actions, they form a DG bimodule.

## References

* W. S. Massey, *Singular Homology Theory*, GTM 70, Springer, 1980, Chapter VII.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Morse homology with differential graded
  coefficients*, Progress in Mathematics 360, Birkhäuser, 2025, Chapter 2 and §7.1.
-/

public section

noncomputable section

open MulOpposite DirectSum

namespace TauCeti

section LeftActMap

variable (G Y : Type*) [TopologicalSpace G] [TopologicalSpace Y] [SMul G Y] [ContinuousSMul G Y]

/-- The left action of `G` on `Y` as a continuous map `G × Y → Y`, `(g, y) ↦ g • y`. -/
def leftActMap : C(G × Y, Y) :=
  ⟨fun x ↦ x.1 • x.2, continuous_smul⟩

@[simp]
theorem leftActMap_apply (x : G × Y) : leftActMap G Y x = x.1 • x.2 :=
  (rfl)

end LeftActMap

namespace NormalizedCubicalChain

section LeftAct

variable (G Y : Type*) [TopologicalSpace G] [TopologicalSpace Y] [SMul G Y] [ContinuousSMul G Y]
  (R : Type*) [CommRing R]

/-- The **left action of chains on `G` on chains on `Y`**: `a · c = act_* (a × c)`. -/
def leftAct (p q : ℕ) :
    NormalizedCubicalChain G R p →ₗ[R] NormalizedCubicalChain Y R q →ₗ[R]
      NormalizedCubicalChain Y R (p + q) :=
  LinearMap.compr₂ (crossProduct G Y R p q) (map R (leftActMap G Y) (p + q))

variable {G Y R}

/-- The left action is the push-forward of the cross product along the action map. -/
theorem leftAct_def {p q : ℕ} (a : NormalizedCubicalChain G R p)
    (c : NormalizedCubicalChain Y R q) :
    leftAct G Y R p q a c = map R (leftActMap G Y) (p + q) (crossProduct G Y R p q a c) :=
  (rfl)

/-- The left action of a cube on a cube is the class of the cube of products. -/
@[simp]
theorem leftAct_ofCube {p q : ℕ} (a : SingularCube G p) (c : SingularCube Y q) :
    leftAct G Y R p q (ofCube G R a) (ofCube Y R c) =
      ofCube Y R ((leftActMap G Y).comp (SingularCube.crossProduct a c)) := by
  simp [leftAct_def]

/-- **The Leibniz rule for the left action**: for `a` of degree `p + 1` and `c` of degree `q + 1`,
`∂ (a · c) = ∂ a · c + (-1) ^ (p + 1) • (a · ∂ c)`, in degree `p + q + 1`. -/
theorem boundary_leftAct {p q : ℕ} (a : NormalizedCubicalChain G R (p + 1))
    (c : NormalizedCubicalChain Y R (q + 1)) :
    boundary Y R (p + q + 1)
        (cast R (by omega : (p + 1) + (q + 1) = (p + q + 1) + 1)
          (leftAct G Y R (p + 1) (q + 1) a c)) =
      leftAct G Y R p (q + 1) (boundary G R p a) c +
        (-1 : R) ^ (p + 1) • cast R (by omega : (p + 1) + q = p + q + 1)
          (leftAct G Y R (p + 1) q a (boundary Y R q c)) := by
  simp only [leftAct_def]
  rw [← map_cast, ← LinearMap.comp_apply (boundary Y R _), ← map_boundary, LinearMap.comp_apply,
    boundary_crossProduct, map_add, map_smul, map_cast]
  rfl

/-- The Leibniz rule for the left action on a `0`-chain. -/
theorem boundary_leftAct_zero_right {p : ℕ} (a : NormalizedCubicalChain G R (p + 1))
    (c : NormalizedCubicalChain Y R 0) :
    boundary Y R p (leftAct G Y R (p + 1) 0 a c) = leftAct G Y R p 0 (boundary G R p a) c := by
  simp only [leftAct_def]
  rw [← LinearMap.comp_apply (boundary Y R p), ← map_boundary, LinearMap.comp_apply,
    boundary_crossProduct_zero_right]
  rfl

/-- The Leibniz rule for the left action of a `0`-chain. -/
theorem boundary_leftAct_zero_left {q : ℕ} (a : NormalizedCubicalChain G R 0)
    (c : NormalizedCubicalChain Y R (q + 1)) :
    boundary Y R q (cast R (Nat.zero_add (q + 1)) (leftAct G Y R 0 (q + 1) a c)) =
      cast R (Nat.zero_add q) (leftAct G Y R 0 q a (boundary Y R q c)) := by
  simp only [leftAct_def]
  rw [← map_cast, ← LinearMap.comp_apply (boundary Y R q), ← map_boundary, LinearMap.comp_apply,
    boundary_crossProduct_zero_left, map_cast]

variable {Y' : Type*} [TopologicalSpace Y'] [SMul G Y'] [ContinuousSMul G Y']

/-- Pushing forward along an equivariant map commutes with the left action. -/
theorem map_leftAct (f : C(Y, Y')) (hf : ∀ (g : G) (y : Y), f (g • y) = g • f y) {p q : ℕ}
    (a : NormalizedCubicalChain G R p) (c : NormalizedCubicalChain Y R q) :
    map R f (p + q) (leftAct G Y R p q a c) = leftAct G Y' R p q a (map R f q c) := by
  have key : f.comp (leftActMap G Y) =
      (leftActMap G Y').comp ((ContinuousMap.id G).prodMap f) := by
    ext x
    simp [hf]
  rw [leftAct_def, leftAct_def, ← LinearMap.comp_apply (map R f (p + q)), ← map_comp, key,
    map_comp, LinearMap.comp_apply, map_crossProduct, map_id, LinearMap.id_apply]

/-- **The left and right actions commute**, after the reindexing `(p + q) + r = p + (q + r)`:
`(a · c) · b = a · (c · b)` for chains `a` on `G`, `c` on `Y` and `b` on `H`. -/
theorem leftAct_act {H : Type*} [TopologicalSpace H] [SMul Hᵐᵒᵖ Y] [ContinuousSMul Hᵐᵒᵖ Y]
    [SMulCommClass G Hᵐᵒᵖ Y] {p q r : ℕ} (a : NormalizedCubicalChain G R p)
    (c : NormalizedCubicalChain Y R q) (b : NormalizedCubicalChain H R r) :
    cast R (Nat.add_assoc p q r) (act Y H R (p + q) r (leftAct G Y R p q a c) b) =
      leftAct G Y R p (q + r) a (act Y H R q r c b) := by
  simp only [act_def, leftAct_def]
  refine map_crossProduct_map_assoc R ?_ a c b
  ext x
  simp [Homeomorph.prodAssoc, Equiv.prodAssoc, smul_comm]

end LeftAct

section SemigroupAction

variable {G Y : Type*} [Semigroup G] [TopologicalSpace G] [TopologicalSpace Y]
  [SemigroupAction G Y] [ContinuousSMul G Y] {R : Type*} [CommRing R]

/-- **Strict associativity of the left action**, after the reindexing
`(p + q) + r = p + (q + r)`: `(a b) · c = a · (b · c)`. -/
theorem leftAct_assoc [ContinuousMul G] {p q r : ℕ} (a : NormalizedCubicalChain G R p)
    (b : NormalizedCubicalChain G R q) (c : NormalizedCubicalChain Y R r) :
    cast R (Nat.add_assoc p q r) (leftAct G Y R (p + q) r (mul G R p q a b) c) =
      leftAct G Y R p (q + r) a (leftAct G Y R q r b c) := by
  simp only [leftAct_def, mul_def]
  refine map_crossProduct_map_assoc R ?_ a b c
  ext x
  simp [Homeomorph.prodAssoc, Equiv.prodAssoc, mul_smul]

end SemigroupAction

section MulAction

variable {G Y : Type*} [Monoid G] [TopologicalSpace G] [TopologicalSpace Y] [MulAction G Y]
  [ContinuousSMul G Y] {R : Type*} [CommRing R]

/-- **The unit acts trivially from the left**, after the reindexing `0 + q = q`. -/
@[simp]
theorem one_leftAct {q : ℕ} (c : NormalizedCubicalChain Y R q) :
    cast R (Nat.zero_add q) (leftAct G Y R 0 q (one G R) c) = c := by
  have h : (leftActMap G Y).comp
      (ContinuousMap.prodMk (ContinuousMap.const Y (1 : G)) (ContinuousMap.id Y)) =
        ContinuousMap.id Y := by
    ext x
    simp
  rw [leftAct_def, one_def, ← map_cast, crossProduct_point_left, ← LinearMap.comp_apply,
    ← map_comp, h, map_id, LinearMap.id_apply]

end MulAction

end NormalizedCubicalChain

open NormalizedCubicalChain

section LeftAction

variable (G Y H : Type*) [Monoid G] [TopologicalSpace G] [ContinuousMul G] [TopologicalSpace Y]
  [MulAction G Y] [ContinuousSMul G Y] (R : Type*) [CommRing R]

/-- The left action of a homogeneous chain of `G` on a homogeneous chain of `Y`, landing in the
module. -/
def cubicalChainLeftActLof (p q : ℕ) :
    NormalizedCubicalChain G R p →ₗ[R] NormalizedCubicalChain Y R q →ₗ[R]
      cubicalChainModule Y H R :=
  (leftAct G Y R p q).compr₂ (cubicalChainModuleLof Y H R (p + q))

/-- The left action as a bilinear map `A × M → M`, `(a, m) ↦ a · m`. -/
def cubicalChainLeftActBilin :
    normalizedCubicalChainAlgebra G R →ₗ[R] cubicalChainModule Y H R →ₗ[R]
      cubicalChainModule Y H R :=
  DirectSum.toModule R ℕ (cubicalChainModule Y H R →ₗ[R] cubicalChainModule Y H R) fun p ↦
    (cubicalChainModuleDesc (G := H) fun q ↦ (cubicalChainLeftActLof G Y H R p q).flip).flip

variable {G Y H R}

omit [ContinuousMul G] in
/-- The left action on homogeneous elements. -/
@[simp]
theorem cubicalChainLeftActBilin_lof_lof {p q : ℕ} (a : NormalizedCubicalChain G R p)
    (c : NormalizedCubicalChain Y R q) :
    cubicalChainLeftActBilin G Y H R (cubicalChainLof G R p a) (cubicalChainModuleLof Y H R q c) =
      cubicalChainModuleLof Y H R (p + q) (leftAct G Y R p q a c) := by
  rw [cubicalChainLeftActBilin, DirectSum.toModule_lof, LinearMap.flip_apply,
    cubicalChainModuleDesc_lof]
  rfl

omit [ContinuousMul G] in
/-- The unit acts trivially on the module from the left. -/
theorem cubicalChainLeftActBilin_one (m : cubicalChainModule Y H R) :
    cubicalChainLeftActBilin G Y H R 1 m = m := by
  have h1 : (1 : normalizedCubicalChainAlgebra G R) = cubicalChainLof G R 0 (one G R) := by
    rw [DirectSum.lof_eq_of]
    rfl
  rw [h1]
  induction m using cubicalChainModule.induction_on with
  | zero => simp
  | lof n c =>
    rw [cubicalChainLeftActBilin_lof_lof, ← cubicalChainModuleLof_cast (Nat.zero_add n),
      one_leftAct]
  | add m m' hm hm' => rw [map_add, hm, hm']

/-- The left action is associative: `(a b) · m = a · (b · m)`. -/
theorem cubicalChainLeftActBilin_mul (a b : normalizedCubicalChainAlgebra G R)
    (m : cubicalChainModule Y H R) :
    cubicalChainLeftActBilin G Y H R (a * b) m =
      cubicalChainLeftActBilin G Y H R a (cubicalChainLeftActBilin G Y H R b m) := by
  induction m using cubicalChainModule.induction_on with
  | zero => simp
  | add m m' hm hm' => simp only [map_add, hm, hm']
  | lof r c =>
    induction a using DirectSum.induction_on with
    | zero => simp
    | add a a' ha ha' => simp only [add_mul, map_add, LinearMap.add_apply, ha, ha']
    | of p x =>
      induction b using DirectSum.induction_on with
      | zero => simp
      | add b b' hb hb' => simp only [mul_add, map_add, LinearMap.add_apply, hb, hb']
      | of q y =>
        rw [← DirectSum.lof_eq_of R, ← DirectSum.lof_eq_of R, cubicalChainLof_mul,
          cubicalChainLeftActBilin_lof_lof, cubicalChainLeftActBilin_lof_lof,
          cubicalChainLeftActBilin_lof_lof, ← leftAct_assoc, cubicalChainModuleLof_cast]

variable (G Y H R)

/-- The left action of the chain algebra of `G` on the module, as a ring homomorphism to the
endomorphisms. -/
def cubicalChainLeftActHom :
    normalizedCubicalChainAlgebra G R →+* Module.End R (cubicalChainModule Y H R) where
  toFun := cubicalChainLeftActBilin G Y H R
  map_one' := LinearMap.ext fun m ↦ cubicalChainLeftActBilin_one m
  map_mul' a b := LinearMap.ext fun m ↦ cubicalChainLeftActBilin_mul a b m
  map_zero' := map_zero _
  map_add' := map_add _

/-- The chains of a space with a left action of `G` form a left module over the chains of `G`. -/
instance : Module (normalizedCubicalChainAlgebra G R) (cubicalChainModule Y H R) :=
  Module.compHom _ (cubicalChainLeftActHom G Y H R)

variable {G Y H R}

/-- The left action of a chain of `G`. -/
theorem smul_cubicalChainModule (a : normalizedCubicalChainAlgebra G R)
    (m : cubicalChainModule Y H R) : a • m = cubicalChainLeftActBilin G Y H R a m :=
  (rfl)

/-- The left action of a homogeneous chain of `G` on a homogeneous chain of `Y`. -/
@[simp]
theorem lof_smul_cubicalChainModuleLof {p q : ℕ} (a : NormalizedCubicalChain G R p)
    (c : NormalizedCubicalChain Y R q) :
    cubicalChainLof G R p a • cubicalChainModuleLof Y H R q c =
      cubicalChainModuleLof Y H R (p + q) (leftAct G Y R p q a c) :=
  cubicalChainLeftActBilin_lof_lof a c

/-- The ground ring and the chains of `G` act compatibly, since the left action is bilinear. -/
instance : IsScalarTower R (normalizedCubicalChainAlgebra G R) (cubicalChainModule Y H R) where
  smul_assoc r a m := by
    rw [smul_cubicalChainModule, smul_cubicalChainModule, map_smul, LinearMap.smul_apply]

/-- The left action is graded: a chain of `G` of cohomological degree `i` sends the chains of `Y`
of degree `j` to degree `i + j`, as the action adds dimensions. -/
instance : SetLike.GradedSMul (cubicalChainGrading G R) (cubicalChainModuleGrading Y H R) where
  smul_mem := by
    intro i j a m ha hm
    rw [vadd_eq_add]
    rcases (mem_cubicalChainGrading_iff G R).1 ha with rfl | ⟨p, x, hp, rfl⟩
    · rw [zero_smul]
      exact zero_mem _
    rcases mem_cubicalChainModuleGrading_iff.1 hm with rfl | ⟨q, c, hq, rfl⟩
    · rw [smul_zero]
      exact zero_mem _
    rw [lof_smul_cubicalChainModuleLof]
    exact mem_cubicalChainModuleGrading_iff.2 (Or.inr ⟨p + q, _, by push_cast; omega, rfl⟩)

/-- The graded Leibniz rule for the left action on homogeneous chains. -/
theorem cubicalChainModuleDifferential_lof_smul {p q : ℕ} (a : NormalizedCubicalChain G R p)
    (c : NormalizedCubicalChain Y R q) :
    cubicalChainModuleDifferential Y H R
        (cubicalChainLof G R p a • cubicalChainModuleLof Y H R q c) =
      cubicalChainDifferential G R (cubicalChainLof G R p a) • cubicalChainModuleLof Y H R q c +
        (-(p : ℤ)).negOnePow • (cubicalChainLof G R p a •
          cubicalChainModuleDifferential Y H R (cubicalChainModuleLof Y H R q c)) := by
  rw [lof_smul_cubicalChainModuleLof, negOnePow_neg_natCast_smul_cubicalChainModule]
  have h0 : ∀ n : ℕ, ((-1 : R) ^ n) • (0 : cubicalChainModule Y H R) = 0 :=
    fun n ↦ smul_zero (M := R) (A := cubicalChainModule Y H R) _
  -- In each case the dimension of the action reduces definitionally to `0` or to a successor,
  -- so the differential is computed by `cubicalChainModuleDifferential_lof_zero` or `_succ`.
  rcases p with _ | k <;> rcases q with _ | j
  · rw [cubicalChainModuleDifferential_lof_zero, cubicalChainModuleDifferential_lof_zero,
      cubicalChainDifferential_lof_zero, smul_zero, zero_smul, h0, zero_add]
  · have hL : cubicalChainModuleDifferential Y H R
        (cubicalChainModuleLof Y H R (0 + (j + 1)) (leftAct G Y R 0 (j + 1) a c)) =
          cubicalChainModuleLof Y H R (0 + j) (leftAct G Y R 0 j a (boundary Y R j c)) := by
      refine (cubicalChainModuleDifferential_lof_succ (0 + j)
        (leftAct G Y R 0 (j + 1) a c)).trans ?_
      congr 1
      apply cast_injective R (Nat.zero_add j)
      exact (boundary_cast R (Nat.zero_add j) (leftAct G Y R 0 (j + 1) a c)).symm.trans
        (boundary_leftAct_zero_left a c)
    rw [hL, cubicalChainDifferential_lof_zero, cubicalChainModuleDifferential_lof_succ,
      lof_smul_cubicalChainModuleLof, zero_smul, zero_add (M := cubicalChainModule Y H R),
      pow_zero, one_smul]
  · refine (cubicalChainModuleDifferential_lof_succ k (leftAct G Y R (k + 1) 0 a c)).trans ?_
    rw [boundary_leftAct_zero_right, cubicalChainDifferential_lof_succ,
      cubicalChainModuleDifferential_lof_zero, smul_zero, lof_smul_cubicalChainModuleLof, h0,
      add_zero (M := cubicalChainModule Y H R)]
    rfl
  · refine (cubicalChainModuleDifferential_lof_succ (k + 1 + j)
      (leftAct G Y R (k + 1) (j + 1) a c)).trans ?_
    have h' : k + 1 + j = k + j + 1 := by omega
    have e : cast R h' (boundary Y R (k + 1 + j) (leftAct G Y R (k + 1) (j + 1) a c)) =
        leftAct G Y R k (j + 1) (boundary G R k a) c +
          (-1 : R) ^ (k + 1) • cast R h' (leftAct G Y R (k + 1) j a (boundary Y R j c)) :=
      (boundary_cast R h' (leftAct G Y R (k + 1) (j + 1) a c)).symm.trans (boundary_leftAct a c)
    rw [cubicalChainDifferential_lof_succ, cubicalChainModuleDifferential_lof_succ,
      lof_smul_cubicalChainModuleLof, lof_smul_cubicalChainModuleLof,
      ← cubicalChainModuleLof_cast h', e, map_add, map_smul, cubicalChainModuleLof_cast]
    rfl

variable (G Y H R)

/-- **The cubical chains of a space with a left action of a topological monoid `G` form a
differential graded left module** over the DG algebra of cubical chains of `G`.  The monoid `H` is
the phantom parameter of `TauCeti.cubicalChainModule` and plays no role. -/
theorem cubicalChainModule_isDGLeftModule :
    IsDGLeftModule (cubicalChain_isDGAlgebra G R) (cubicalChainModuleGrading Y H R)
      (cubicalChainModuleDifferential Y H R) where
  isHomogeneous := cubicalChainModuleDifferential_isHomogeneous Y H R
  sq_zero := cubicalChainModuleDifferential_cubicalChainModuleDifferential
  leibniz := fun {p} {a} ha m ↦ by
    rcases (mem_cubicalChainGrading_iff G R).1 ha with rfl | ⟨n, x, hn, rfl⟩
    · simp
    obtain rfl : p = -(n : ℤ) := by omega
    induction m using cubicalChainModule.induction_on with
    | zero => simp
    | lof q c => exact cubicalChainModuleDifferential_lof_smul x c
    | add m m' hm hm' =>
      rw [smul_add, map_add, hm, hm', map_add, smul_add, smul_add, smul_add]
      abel

end LeftAction

section LeftMap

universe u

variable {G : Type*} {Y Y' : Type u} {H : Type*} [Monoid G] [TopologicalSpace G] [ContinuousMul G]
  [TopologicalSpace Y] [TopologicalSpace Y'] [MulAction G Y] [ContinuousSMul G Y] [MulAction G Y']
  [ContinuousSMul G Y'] {R : Type*} [CommRing R]

/-- The map of modules induced by a `G`-equivariant map commutes with the left action. -/
theorem cubicalChainModuleLinearMap_smul (f : C(Y, Y'))
    (hf : ∀ (g : G) (y : Y), f (g • y) = g • f y) (a : normalizedCubicalChainAlgebra G R)
    (x : cubicalChainModule Y H R) :
    cubicalChainModuleLinearMap R f (a • x) = a • cubicalChainModuleLinearMap R f x := by
  induction x using cubicalChainModule.induction_on with
  | zero => rw [smul_zero, map_zero, smul_zero]
  | add x x' hx hx' => rw [smul_add, map_add, hx, hx', map_add, smul_add]
  | lof q c =>
    induction a using DirectSum.induction_on with
    | zero => rw [zero_smul, map_zero, zero_smul]
    | add a a' ha ha' => rw [add_smul, map_add, ha, ha', add_smul]
    | of p z =>
      rw [← DirectSum.lof_eq_of R, lof_smul_cubicalChainModuleLof,
        cubicalChainModuleLinearMap_lof, cubicalChainModuleLinearMap_lof,
        lof_smul_cubicalChainModuleLof, map_leftAct f hf]

end LeftMap

section Bimodule

variable (G Y H : Type*) [Monoid G] [TopologicalSpace G] [ContinuousMul G] [TopologicalSpace Y]
  [MulAction G Y] [ContinuousSMul G Y] [Monoid H] [TopologicalSpace H] [ContinuousMul H]
  [MulAction Hᵐᵒᵖ Y] [ContinuousSMul Hᵐᵒᵖ Y] [SMulCommClass G Hᵐᵒᵖ Y] (R : Type*) [CommRing R]

/-- When the actions of `G` and `H` on `Y` commute, so do the actions of their chains. -/
instance : SMulCommClass (normalizedCubicalChainAlgebra G R) (normalizedCubicalChainAlgebra H R)ᵐᵒᵖ
    (cubicalChainModule Y H R) where
  smul_comm a b m := by
    rw [← op_unop b]
    induction m using cubicalChainModule.induction_on with
    | zero => simp only [smul_zero]
    | add m m' hm hm' => simp only [smul_add, hm, hm']
    | lof q c =>
      induction a using DirectSum.induction_on with
      | zero => simp only [zero_smul, smul_zero]
      | add a a' ha ha' => simp only [add_smul, smul_add, ha, ha']
      | of p x =>
        induction b.unop using DirectSum.induction_on with
        | zero => simp only [op_zero, zero_smul, smul_zero]
        | add b b' hb hb' => simp only [op_add, add_smul, smul_add, hb, hb']
        | of r y =>
          rw [← DirectSum.lof_eq_of R, ← DirectSum.lof_eq_of R, lof_smul_cubicalChainModuleLof,
            op_lof_smul_cubicalChainModuleLof, op_lof_smul_cubicalChainModuleLof,
            lof_smul_cubicalChainModuleLof, ← leftAct_act, cubicalChainModuleLof_cast]

/-- **The cubical chains of a space with commuting left and right actions of topological monoids
`G` and `H` form a differential graded `(C_*(G), C_*(H))`-bimodule.** -/
theorem cubicalChainModule_isDGBimodule :
    IsDGBimodule (cubicalChain_isDGAlgebra G R) (cubicalChain_isDGAlgebra H R)
      (cubicalChainModuleGrading Y H R) (cubicalChainModuleDifferential Y H R) where
  toIsDGLeftModule := cubicalChainModule_isDGLeftModule G Y H R
  leibniz_right := (cubicalChainModule_isDGRightModule Y H R).leibniz

end Bimodule

end TauCeti

end
