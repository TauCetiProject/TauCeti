/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.ContMDiff.Sigma
public import TauCeti.Geometry.Manifold.DifferentialOperator.Peetre.Basic
public import TauCeti.Geometry.Manifold.DifferentialOperator.PrincipalSymbol
public import TauCeti.Geometry.Manifold.Instances.Sigma
public import TauCeti.Geometry.Manifold.VectorField.AddCircle

/-!
# Differential operators on disjoint unions of manifolds

The smooth functions on a disjoint union `Σ i, M i` of manifolds on a common model are the
families of smooth functions on the components. Restriction to the component `M i`
(`TauCeti.sigmaRestrict i`) is a surjective algebra homomorphism, since a smooth function on `M i`
extends by zero to the other components. A family of operators `P i` on the smooth functions on
the components assembles into the operator `TauCeti.sigmaOperator P` acting by `P i` on `M i`.
Its commutator with multiplication by `f` is assembled from the commutators of the `P i` with the
restrictions of `f`, so it is a differential operator of order at most `m`, in Grothendieck's
sense of iterated commutators (`TauCeti.differentialOperators`), exactly when every `P i` is.

This gives the example showing that Peetre's theorem bounds the order of a local operator only
over compact sets. On the countable disjoint union `Σ j : ℕ, AddCircle p` of circles, let `P` act
by the `j`-th power `∂_t ^ j` of the derivative on the `j`-th circle. It is local: `(P f) x = 0`
when `f` vanishes near `x`. A compact set meets only finitely many circles, and the order of `P`
is bounded over it, as Peetre's theorem
(`LinearMap.exists_apply_eq_zero_of_mem_smoothVanishingIdeal_pow`) asserts. But `∂_t ^ (r + 1)`
does not have order at most `r`, so `P` is not a differential operator of any finite order. The
compactness hypothesis of
`LinearMap.exists_mem_differentialOperators_iff_apply_eq_zero_of_eventuallyEq`, which identifies
local operators with differential operators, therefore cannot be dropped.

## Main declarations

* `TauCeti.sigmaRestrict`: restriction of smooth functions to a component, an algebra
  homomorphism; it is surjective (`TauCeti.sigmaRestrict_surjective`).
* `TauCeti.sigmaOperator`: the operator acting componentwise by a family of operators, an algebra
  homomorphism from families of operators.
* `TauCeti.smulCommutator_sigmaOperator`: commutators with multiplication are taken
  componentwise.
* `TauCeti.sigmaOperator_mem_differentialOperators_iff`: the componentwise operator has order at
  most `m` exactly when each of its components has.
* `TauCeti.sigmaOperator_apply_eq_zero_of_eventuallyEq`: the componentwise operator of local
  operators is local.
* `AddCircle.sigmaOperator_pow_timeDerivation_apply_eq_zero_of_eventuallyEq`,
  `AddCircle.exists_sigmaOperator_pow_timeDerivation_apply_eq_zero_of_mem_smoothVanishingIdeal_pow`
  and `AddCircle.sigmaOperator_pow_timeDerivation_notMem_differentialOperators`: the operator
  acting by `∂_t ^ j` on the `j`-th of countably many circles is local, has finite order over each
  compact set, and has no finite order.

## References

* J. Peetre, *Réctification à l'article « Une caractérisation abstraite des opérateurs
  différentiels »*, Math. Scand. 8 (1960), 116–120.
* I. Kolář, P. W. Michor, J. Slovák, *Natural Operations in Differential Geometry*, Springer,
  1993, Theorem 19.1 (Peetre's theorem: local finite order over compact sets).
-/

public section

noncomputable section

open Filter
open scoped ContDiff Manifold Topology

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {ι : Type*} {M : ι → Type*} [∀ i, TopologicalSpace (M i)]
  [∀ i, ChartedSpace H (M i)]

/-! ### Restriction to a component -/

/-- Restriction of smooth functions on a disjoint union `Σ i, M i` to the component `M i`, as an
algebra homomorphism. -/
def sigmaRestrict (i : ι) : C^∞⟮I, Σ i, M i; ℝ⟯ →ₐ[ℝ] C^∞⟮I, M i; ℝ⟯ :=
  ContMDiffMap.compRightAlgHom ℝ ℝ
    (⟨Sigma.mk i, contMDiff_sigmaMk i⟩ : C^∞⟮I, M i; I, Σ i, M i⟯)

@[simp]
theorem sigmaRestrict_apply (i : ι) (f : C^∞⟮I, Σ i, M i; ℝ⟯) (x : M i) :
    sigmaRestrict i f x = f ⟨i, x⟩ := by
  have h := ContMDiffMap.compRightAlgHom_apply (𝕜 := ℝ) ℝ
    (⟨Sigma.mk i, contMDiff_sigmaMk i⟩ : C^∞⟮I, M i; I, Σ i, M i⟯) f
  exact congr($h x).trans (ContMDiffMap.comp_apply _ _ x)

/-- Every smooth function on a component extends, by zero, to a smooth function on the disjoint
union. -/
theorem sigmaRestrict_surjective (i : ι) :
    Function.Surjective (sigmaRestrict (I := I) (M := M) i) := by
  classical
  intro g
  have hext (x : M i) : Function.extend (Sigma.mk i) g 0 ⟨i, x⟩ = g x :=
    sigma_mk_injective.extend_apply _ _ x
  refine ⟨⟨Function.extend (Sigma.mk i) g 0, contMDiff_sigma_iff.2 fun j ↦ ?_⟩,
    ContMDiffMap.ext fun x ↦ (sigmaRestrict_apply i _ x).trans (hext x)⟩
  by_cases hj : j = i
  · subst hj
    exact g.contMDiff.congr hext
  · refine (contMDiff_const (c := (0 : ℝ))).congr fun x ↦ ?_
    refine Function.extend_apply' _ _ _ ?_
    rintro ⟨y, hy⟩
    exact hj (congrArg Sigma.fst hy).symm

/-! ### Componentwise operators -/

/-- The operator acting by `P i` on the component `M i`, before bundling. -/
private def sigmaOperatorAux (P : ∀ i, Module.End ℝ C^∞⟮I, M i; ℝ⟯) :
    Module.End ℝ C^∞⟮I, Σ i, M i; ℝ⟯ where
  toFun f := ⟨fun x ↦ P x.1 (sigmaRestrict x.1 f) x.2,
    contMDiff_sigma_iff.2 fun i ↦ (P i (sigmaRestrict i f)).contMDiff⟩
  map_add' f g := by ext; simp only [map_add]; rfl
  map_smul' c f := by ext; simp only [map_smul]; rfl

private theorem sigmaOperatorAux_apply (P : ∀ i, Module.End ℝ C^∞⟮I, M i; ℝ⟯)
    (f : C^∞⟮I, Σ i, M i; ℝ⟯) (x : Σ i, M i) :
    sigmaOperatorAux P f x = P x.1 (sigmaRestrict x.1 f) x.2 :=
  (rfl)

private theorem sigmaRestrict_sigmaOperatorAux (P : ∀ i, Module.End ℝ C^∞⟮I, M i; ℝ⟯) (i : ι)
    (f : C^∞⟮I, Σ i, M i; ℝ⟯) :
    sigmaRestrict i (sigmaOperatorAux P f) = P i (sigmaRestrict i f) := by
  ext x
  rw [sigmaRestrict_apply]
  rfl

/-- The operator on the smooth functions on a disjoint union `Σ i, M i` acting by `P i` on the
component `M i`, as an algebra homomorphism from families of operators. -/
def sigmaOperator :
    (∀ i, Module.End ℝ C^∞⟮I, M i; ℝ⟯) →ₐ[ℝ] Module.End ℝ C^∞⟮I, Σ i, M i; ℝ⟯ where
  toFun := sigmaOperatorAux
  map_one' := by ext f ⟨i, x⟩; simp [sigmaOperatorAux_apply]
  map_mul' P Q := by
    ext f ⟨i, x⟩
    simp [sigmaOperatorAux_apply, sigmaRestrict_sigmaOperatorAux]
  map_zero' := by ext f ⟨i, x⟩; simp [sigmaOperatorAux_apply]
  map_add' _ _ := by ext f ⟨i, x⟩; simp [sigmaOperatorAux_apply]
  commutes' r := by
    ext f ⟨i, x⟩
    simp [sigmaOperatorAux_apply, Module.algebraMap_end_apply]

@[simp]
theorem sigmaOperator_apply_mk (P : ∀ i, Module.End ℝ C^∞⟮I, M i; ℝ⟯)
    (f : C^∞⟮I, Σ i, M i; ℝ⟯) (i : ι) (x : M i) :
    sigmaOperator P f ⟨i, x⟩ = P i (sigmaRestrict i f) x :=
  (rfl)

/-- Restricting the componentwise operator to `M i` gives its component `P i`. -/
@[simp]
theorem sigmaRestrict_sigmaOperator (P : ∀ i, Module.End ℝ C^∞⟮I, M i; ℝ⟯) (i : ι)
    (f : C^∞⟮I, Σ i, M i; ℝ⟯) :
    sigmaRestrict i (sigmaOperator P f) = P i (sigmaRestrict i f) :=
  sigmaRestrict_sigmaOperatorAux P i f

/-- The commutator of the componentwise operator with multiplication by `f` is the componentwise
operator of the commutators with the restrictions of `f`. -/
theorem smulCommutator_sigmaOperator (f : C^∞⟮I, Σ i, M i; ℝ⟯)
    (P : ∀ i, Module.End ℝ C^∞⟮I, M i; ℝ⟯) :
    smulCommutator ℝ f (sigmaOperator P) =
      sigmaOperator fun i ↦ smulCommutator ℝ (sigmaRestrict i f) (P i) := by
  ext g ⟨i, x⟩
  simp

/-- The componentwise operator has order at most `m` exactly when each of its components has. -/
theorem sigmaOperator_mem_differentialOperators_iff {P : ∀ i, Module.End ℝ C^∞⟮I, M i; ℝ⟯}
    {m : ℕ} :
    sigmaOperator P ∈
        differentialOperators ℝ C^∞⟮I, Σ i, M i; ℝ⟯ C^∞⟮I, Σ i, M i; ℝ⟯ C^∞⟮I, Σ i, M i; ℝ⟯ m ↔
      ∀ i, P i ∈ differentialOperators ℝ C^∞⟮I, M i; ℝ⟯ C^∞⟮I, M i; ℝ⟯ C^∞⟮I, M i; ℝ⟯ m := by
  refine ⟨fun h i ↦ mem_differentialOperators_of_comp_eq_comp (sigmaRestrict_surjective i)
    (LinearMap.ext fun f ↦ (sigmaRestrict_sigmaOperator P i f).symm) h, fun h ↦ ?_⟩
  induction m generalizing P with
  | zero =>
    refine mem_differentialOperators_zero_iff_smulCommutator.2 fun f ↦ ?_
    simp_rw [smulCommutator_sigmaOperator,
      smulCommutator_eq_zero_of_mem_differentialOperators_zero (h _)]
    exact map_zero sigmaOperator
  | succ m ih =>
    refine mem_differentialOperators_succ_iff.2 fun f ↦ ?_
    rw [smulCommutator_sigmaOperator]
    exact ih fun i ↦ smulCommutator_mem_differentialOperators (h i) _

/-- The componentwise operator of local operators is local: its value at `x` vanishes on every
function vanishing near `x`. -/
theorem sigmaOperator_apply_eq_zero_of_eventuallyEq {P : ∀ i, Module.End ℝ C^∞⟮I, M i; ℝ⟯}
    (hP : ∀ i (f : C^∞⟮I, M i; ℝ⟯) (x : M i), (f : M i → ℝ) =ᶠ[𝓝 x] 0 → P i f x = 0)
    {f : C^∞⟮I, Σ i, M i; ℝ⟯} {x : Σ i, M i} (hf : (f : (Σ i, M i) → ℝ) =ᶠ[𝓝 x] 0) :
    sigmaOperator P f x = 0 := by
  obtain ⟨i, y⟩ := x
  refine hP i _ y ?_
  filter_upwards [(continuous_sigmaMk.tendsto y).eventually hf] with z hz
  simpa using hz

end TauCeti

/-! ### Countably many circles -/

namespace AddCircle

open TauCeti

variable (p : ℝ) [Fact (0 < p)]

/-- On the disjoint union of countably many circles, the operator acting by `∂_t ^ j` on the
`j`-th circle is local. -/
theorem sigmaOperator_pow_timeDerivation_apply_eq_zero_of_eventuallyEq
    {f : C^∞⟮𝓘(ℝ), Σ _ : ℕ, AddCircle p; ℝ⟯} {x : Σ _ : ℕ, AddCircle p}
    (hf : (f : (Σ _ : ℕ, AddCircle p) → ℝ) =ᶠ[𝓝 x] 0) :
    sigmaOperator (fun j ↦ (timeDerivation p : Module.End ℝ C^∞⟮𝓘(ℝ), AddCircle p; ℝ⟯) ^ j) f
      x = 0 :=
  sigmaOperator_apply_eq_zero_of_eventuallyEq (fun j g y hg ↦ by
    simpa using differentialOperators_apply_eq_of_eventuallyEq
      (SetLike.pow_mem_graded j (timeDerivation p).mem_differentialOperators_one)
      BoundarylessManifold.isInteriorPoint (g := 0) hg) hf

/-- On the disjoint union of countably many circles, the operator acting by `∂_t ^ j` on the
`j`-th circle has finite order over every compact set `K`: for some `r`, its value at each point
`x ∈ K` vanishes on the `(r + 1)`-st power of the ideal of smooth functions vanishing at `x`. -/
theorem exists_sigmaOperator_pow_timeDerivation_apply_eq_zero_of_mem_smoothVanishingIdeal_pow
    {K : Set (Σ _ : ℕ, AddCircle p)} (hK : IsCompact K) :
    ∃ r : ℕ, ∀ x ∈ K, ∀ f ∈ smoothVanishingIdeal 𝓘(ℝ) x ^ (r + 1),
      sigmaOperator (fun j ↦ (timeDerivation p : Module.End ℝ C^∞⟮𝓘(ℝ), AddCircle p; ℝ⟯) ^ j) f
        x = 0 :=
  LinearMap.exists_apply_eq_zero_of_mem_smoothVanishingIdeal_pow
    (ContMDiffMap.coeFnLinearMap ∘ₗ
      sigmaOperator fun j ↦ (timeDerivation p : Module.End ℝ C^∞⟮𝓘(ℝ), AddCircle p; ℝ⟯) ^ j)
    isOpen_univ
    (fun _ _ _ hf ↦ sigmaOperator_pow_timeDerivation_apply_eq_zero_of_eventuallyEq p hf)
    (fun f ↦ (sigmaOperator _ f).contMDiff.continuous.continuousOn) hK (Set.subset_univ K)

/-- **Peetre's theorem gives no global order bound.** On the disjoint union of countably many
circles, the operator acting by `∂_t ^ j` on the `j`-th circle is not a differential operator of
any finite order `r`, since `∂_t ^ (r + 1)` does not have order at most `r`. -/
theorem sigmaOperator_pow_timeDerivation_notMem_differentialOperators (r : ℕ) :
    sigmaOperator (fun j ↦ (timeDerivation p : Module.End ℝ C^∞⟮𝓘(ℝ), AddCircle p; ℝ⟯) ^ j) ∉
      differentialOperators ℝ C^∞⟮𝓘(ℝ), Σ _ : ℕ, AddCircle p; ℝ⟯
        C^∞⟮𝓘(ℝ), Σ _ : ℕ, AddCircle p; ℝ⟯ C^∞⟮𝓘(ℝ), Σ _ : ℕ, AddCircle p; ℝ⟯ r :=
  fun h ↦ timeDerivation_ne_zero p <| (Derivation.pow_succ_mem_differentialOperators_iff _ r).1 <|
    sigmaOperator_mem_differentialOperators_iff.1 h (r + 1)

end AddCircle
