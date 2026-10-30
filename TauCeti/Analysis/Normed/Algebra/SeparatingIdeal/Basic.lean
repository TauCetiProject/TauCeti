/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.Mul
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import TauCeti.Analysis.Normed.Operator.SeparatingSpace

/-!
# Separating ideals

A closed two-sided ideal `J` of a topological algebra `B` is a *separating ideal* when, for
every sequence `b` in `B`, the two nests of closed subspaces
`closure (b 0 ⋯ b (n - 1) J)` and `closure (J b (n - 1) ⋯ b 0)` are eventually constant.
Separating ideals are the algebraic shadow of Sinclair's stability lemma: the separating space
of a surjective algebra homomorphism, or more generally of a linear map into `B` whose
commutators with the actions of `B` are continuous, is a separating ideal. The structure theory
of separating ideals in semisimple algebras builds on this to prove the classical
automatic-continuity theorems.

The nests are written with products in `Module.End R B` of the multiplication operators
`LinearMap.mulLeft R (b i)` and `LinearMap.mulRight R (b i)`, so that no identity of `B` is
needed and the `0`-th term of each nest is the closure of `J` itself.

## Main definitions

* `Submodule.IsSeparatingIdeal`: a closed two-sided ideal, given as a scalar submodule, whose
  left and right nests stabilize along every sequence.

## Main results

* `Submodule.isSeparatingIdeal_of_finiteDimensional`: a finite-dimensional two-sided ideal is
  a separating ideal.
* `LinearMap.isSeparatingIdeal_separatingSpace`: if `T : E → B` is a linear map between Banach
  spaces, `B` a Banach algebra, and `x ↦ T (L b x) - b * T x` and `x ↦ T (R b x) - T x * b` are
  continuous for continuous linear operators `L b` and `R b` on `E`, then the separating space
  of `T` is a separating ideal. This applies to Banach `B`-bimodules with actions `L` and `R`.
* `NonUnitalAlgHom.isSeparatingIdeal_separatingSpace`: the separating space of a surjective
  homomorphism between Banach algebras, not assumed continuous, is a separating ideal.

## References

* H. G. Dales, *Banach Algebras and Automatic Continuity*, §5.2: separating ideals and the
  separating spaces of homomorphisms and intertwining maps.
* A. M. Sinclair, *Automatic Continuity of Linear Operators*, London Math. Soc. Lecture Note
  Series 21.
-/

public section

open Filter

namespace Submodule

section Defs

variable {R B : Type*} [CommSemiring R] [NonUnitalSemiring B] [Module R B]
  [IsScalarTower R B B] [SMulCommClass R B B] [TopologicalSpace B] [ContinuousAdd B]
  [ContinuousConstSMul R B]

/-- A *separating ideal* of a topological algebra `B` is a closed two-sided ideal `J`, given as a
scalar submodule, such that for every sequence `b` in `B` the nests of closed subspaces
`closure (b 0 ⋯ b (n - 1) J)` and `closure (J b (n - 1) ⋯ b 0)` are eventually constant. The
products are formed in `Module.End R B` from left and right multiplication operators. -/
structure IsSeparatingIdeal (J : Submodule R B) : Prop where
  /-- A separating ideal is closed. -/
  isClosed : IsClosed (J : Set B)
  /-- A separating ideal is a left ideal. -/
  mul_mem_left (b : B) {y : B} : y ∈ J → b * y ∈ J
  /-- A separating ideal is a right ideal. -/
  mul_mem_right (b : B) {y : B} : y ∈ J → y * b ∈ J
  /-- The left nest `closure (b 0 ⋯ b (n - 1) J)` is eventually constant. -/
  eventuallyConst_left (b : ℕ → B) : EventuallyConst (fun n ↦
    (J.map ((List.range n).map fun i ↦ LinearMap.mulLeft R (b i)).prod).topologicalClosure) atTop
  /-- The right nest `closure (J b (n - 1) ⋯ b 0)` is eventually constant. -/
  eventuallyConst_right (b : ℕ → B) : EventuallyConst (fun n ↦
    (J.map ((List.range n).map fun i ↦ LinearMap.mulRight R (b i)).prod).topologicalClosure) atTop

end Defs

section FiniteDimensional

variable {𝕜 B : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] [NonUnitalRing B]
  [Module 𝕜 B] [IsScalarTower 𝕜 B B] [SMulCommClass 𝕜 B B] [TopologicalSpace B]
  [IsTopologicalAddGroup B] [ContinuousSMul 𝕜 B] [T2Space B]

/-- A finite-dimensional two-sided ideal of a Hausdorff topological algebra over a complete field
is a separating ideal: its nests are decreasing chains of finite-dimensional, hence closed,
subspaces. -/
theorem isSeparatingIdeal_of_finiteDimensional (J : Submodule 𝕜 B) [FiniteDimensional 𝕜 J]
    (hleft : ∀ (b : B) {y : B}, y ∈ J → b * y ∈ J)
    (hright : ∀ (b : B) {y : B}, y ∈ J → y * b ∈ J) : J.IsSeparatingIdeal := by
  -- A decreasing chain of finite-dimensional subspaces is eventually constant.
  have key {f : ℕ → Module.End 𝕜 B} (hf : ∀ n, J.map (f n) ≤ J) :
      EventuallyConst (fun n ↦ (J.map ((List.range n).map f).prod).topologicalClosure) atTop := by
    have hanti : Antitone fun n ↦ J.map ((List.range n).map f).prod :=
      antitone_nat_of_succ_le fun n ↦ by
        simpa [List.range_succ, Module.End.mul_eq_comp, Submodule.map_comp] using
          Submodule.map_mono (hf n)
    simp_rw [(J.map _).closed_of_finiteDimensional.submodule_topologicalClosure_eq]
    obtain ⟨k, hk⟩ := WellFoundedLT.antitone_chain_condition
      (f := fun n ↦ Module.finrank 𝕜 (J.map ((List.range n).map f).prod))
      fun m n h ↦ Submodule.finrank_mono (hanti h)
    exact eventuallyConst_atTop.2 ⟨k, fun m hm ↦ eq_of_le_of_finrank_eq (hanti hm) (hk m hm).symm⟩
  refine ⟨J.closed_of_finiteDimensional, hleft, hright, fun b ↦ key ?_, fun b ↦ key ?_⟩
  · rintro n _ ⟨y, hy, rfl⟩
    exact hleft (b n) hy
  · rintro n _ ⟨y, hy, rfl⟩
    exact hright (b n) hy

end FiniteDimensional

end Submodule

namespace LinearMap

variable {𝕜 E B : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  [NonUnitalNormedRing B] [NormedSpace 𝕜 B] [IsScalarTower 𝕜 B B] [SMulCommClass 𝕜 B B]
  [CompleteSpace B]

/-- **Separating spaces of intertwining maps are separating ideals.** Let `T : E → B` be a linear
map, not assumed continuous, from a Banach space into a Banach algebra, and let `L b` and `R b`
be continuous linear operators on `E` such that `x ↦ T (L b x) - b * T x` and
`x ↦ T (R b x) - T x * b` are continuous for each `b`. Then the separating space of `T` is a
separating ideal of `B`. This applies to a Banach `B`-bimodule `E` with actions `L` and `R`; the
bimodule laws themselves are not needed. -/
theorem isSeparatingIdeal_separatingSpace (T : E →ₗ[𝕜] B) (L R : B → E →L[𝕜] E)
    (hL : ∀ b, Continuous fun x ↦ T (L b x) - b * T x)
    (hR : ∀ b, Continuous fun x ↦ T (R b x) - T x * b) :
    T.separatingSpace.IsSeparatingIdeal := by
  -- Sinclair's stability lemma for products `M 0 ⋯ M (n - 1)` of continuous operators that
  -- intertwine `T` with continuous operators `P n` on `E` up to continuous errors.
  have key {M : ℕ → Module.End 𝕜 B} (hM : ∀ n, Continuous (M n)) {P : ℕ → E →L[𝕜] E}
      (hPM : ∀ n, Continuous (M n ∘ₗ T - T ∘ₗ (P n : E →ₗ[𝕜] E))) :
      EventuallyConst (fun n ↦ (T.separatingSpace.map
        ((List.range n).map M).prod).topologicalClosure) atTop := by
    let Q : ℕ → B →L[𝕜] B := fun n ↦ ⟨M n, hM n⟩
    have h := T.eventuallyConst_topologicalClosure_map_separatingSpace P Q hPM
      (V := fun n ↦ ((List.range n).map Q).prod) rfl
      (fun n ↦ by simp [List.range_succ, ContinuousLinearMap.mul_def])
    convert h using 4 with n
    rw [← ContinuousLinearMap.toLinearMapRingHom_apply, map_list_prod, List.map_map]
    simp [Q, Function.comp_def]
  -- The continuity hypotheses, as intertwining relations with the multiplication operators.
  have hl (b : B) : Continuous (mulLeft 𝕜 b) :=
    (continuous_const_mul b).congr fun x ↦ by simp
  have hr (b : B) : Continuous (mulRight 𝕜 b) :=
    (continuous_mul_const b).congr fun x ↦ by simp
  have hL' (b : B) : Continuous (mulLeft 𝕜 b ∘ₗ T - T ∘ₗ (L b : E →ₗ[𝕜] E)) :=
    (hL b).neg.congr fun x ↦ by simp
  have hR' (b : B) : Continuous (mulRight 𝕜 b ∘ₗ T - T ∘ₗ (R b : E →ₗ[𝕜] E)) :=
    (hR b).neg.congr fun x ↦ by simp
  exact
    { isClosed := T.isClosed_separatingSpace
      mul_mem_left := fun b y hy ↦ T.map_separatingSpace_le_of_continuous_sub T
        ⟨mulLeft 𝕜 b, hl b⟩ (L b) (hL' b) ⟨y, hy, rfl⟩
      mul_mem_right := fun b y hy ↦ T.map_separatingSpace_le_of_continuous_sub T
        ⟨mulRight 𝕜 b, hr b⟩ (R b) (hR' b) ⟨y, hy, rfl⟩
      eventuallyConst_left := fun b ↦ key (fun n ↦ hl (b n)) fun n ↦ hL' (b n)
      eventuallyConst_right := fun b ↦ key (fun n ↦ hr (b n)) fun n ↦ hR' (b n) }

end LinearMap

namespace NonUnitalAlgHom

variable {𝕜 A B : Type*} [NontriviallyNormedField 𝕜]
  [NonUnitalNormedRing A] [NormedSpace 𝕜 A] [IsScalarTower 𝕜 A A] [SMulCommClass 𝕜 A A]
  [CompleteSpace A]
  [NonUnitalNormedRing B] [NormedSpace 𝕜 B] [IsScalarTower 𝕜 B B] [SMulCommClass 𝕜 B B]
  [CompleteSpace B]

/-- **The separating space of a surjective homomorphism is a separating ideal.** For a surjective
homomorphism `θ : A → B` of Banach algebras, not assumed continuous, the separating space of
`θ` is a separating ideal of `B`. -/
theorem isSeparatingIdeal_separatingSpace (θ : A →ₙₐ[𝕜] B) (hθ : Function.Surjective θ) :
    (θ : A →ₗ[𝕜] B).separatingSpace.IsSeparatingIdeal := by
  -- Multiplying by `b = θ a` in `B` is intertwined by `θ` with multiplying by `a` in `A`.
  refine (θ : A →ₗ[𝕜] B).isSeparatingIdeal_separatingSpace
    (fun b ↦ ContinuousLinearMap.mul 𝕜 A (Function.surjInv hθ b))
    (fun b ↦ (ContinuousLinearMap.mul 𝕜 A).flip (Function.surjInv hθ b)) (fun b ↦ ?_) fun b ↦ ?_
  · simpa [Function.surjInv_eq hθ] using continuous_const (y := (0 : B))
  · simpa [Function.surjInv_eq hθ] using continuous_const (y := (0 : B))

end NonUnitalAlgHom
