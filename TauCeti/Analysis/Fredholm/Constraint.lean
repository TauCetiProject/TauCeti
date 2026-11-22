/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Exact.Basic
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient
public import TauCeti.Analysis.Fredholm.Prod
import Mathlib.LinearAlgebra.Isomorphisms
import TauCeti.LinearAlgebra.Exact

/-!
# Linearizations extended by finitely many constraints

Moduli spaces of pseudoholomorphic curves are often cut down by finitely many conditions:
a marked point is required to map into a cycle, a Floer end is matched with an incidence
condition, or the curve is normalized by a slice condition. Linearizing at a solution, the
equation contributes a continuous linear map `D : E →L[𝕜] F`, the conditions contribute a
continuous linear map `L : E →L[𝕜] G` to a finite-dimensional space `G`, typically an evaluation
map followed by the projection to the normal space of the constraint, and the linearization of
the constrained problem is the **extended operator** `D.prod L : E →L[𝕜] F × G`. The constrained
problem is regular when `D.prod L` is onto, and its kernel `ker D ⊓ ker L`
(`ContinuousLinearMap.ker_prod`) is then the candidate tangent space to the constrained moduli
space.

This file is the target-side counterpart of `TauCeti.Analysis.Fredholm.Parametric`, which treats
the domain extension `D₁.coprod D₂` by parameter directions. Everything is read off the exact
sequence
```text
0 → ker (D.prod L) → ker D → G → (F × G) ⧸ range (D.prod L) → F ⧸ range D → 0,
```
whose maps are the inclusion, the restriction `L.domRestrict D.ker` of the constraint map to the
kernel of `D`, the map `g ↦ [(0, g)]` (`ContinuousLinearMap.constraintToCoker`), and the map
induced by the first projection (`ContinuousLinearMap.cokerProdHom`). Exactness at the three
inner terms is `ContinuousLinearMap.ker_domRestrict_eq_comap_ker_prod`,
`ContinuousLinearMap.exact_domRestrict_constraintToCoker` and
`ContinuousLinearMap.exact_constraintToCoker_cokerProdHom`, with no hypotheses.

* **Regularity of the constrained problem.** `D.prod L` is onto exactly when `D` is onto and the
  constraint map is onto on the kernel of `D` (`ContinuousLinearMap.surjective_prod_iff`). For a
  constraint `L = (G ⧸ N) ∘ ev` cutting `G` down to a subspace `N`, the second condition reads
  `ev (ker D) ⊔ N = ⊤`: the evaluation map on the solutions of the linearized equation is
  transverse to the constraint (`ContinuousLinearMap.surjective_prod_mkQL_comp_iff`). When `D`
  is onto, the cokernel of the extended operator is the cokernel `G ⧸ L (ker D)` of the
  constraint map on the kernel (`ContinuousLinearMap.constraintCokerEquiv`).
* **Dimensions.** The kernel shrinks by the rank of the constraint map on `ker D`
  (`ContinuousLinearMap.finrank_ker_prod_add_finrank_range_domRestrict`), and the cokernel grows
  by its corank (`ContinuousLinearMap.finrank_quotient_range_prod_add_finrank_range_domRestrict`).
  Hence imposing the constraints lowers the index by `dim G`
  (`ContinuousLinearMap.index_prod`), whether or not the extended operator is onto; for an
  incidence condition with a subspace `N`, where the constraint space is `G ⧸ N`, this is the
  codimension of `N`. For an onto `D`, the extended operator is onto exactly when its kernel has
  the expected dimension (`ContinuousLinearMap.surjective_prod_iff_finrank_ker_add`).
* **Fredholmness.** Over a complete scalar field, with Hausdorff topological vector spaces and
  finite-dimensional `G`, the extended operator is Fredholm exactly when `D` is
  (`ContinuousLinearMap.isFredholm_prod_iff`): `D.prod L` differs from `(x ↦ (D x, 0))` by an
  operator of finite rank.

The exact sequence and the surjectivity criterion hold over any ring; the dimension formulas
need a division ring and the stated finite dimensions, and none of them needs the Fredholm
property.

## References

* D. McDuff, D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS Colloquium
  Publications 52, 2012, Section 3.4 (evaluation maps and transversality to cycles) and
  Appendix A.1 (Fredholm operators).
-/

public section

namespace ContinuousLinearMap

open Module

section Ring

variable {𝕜 : Type*} [Ring 𝕜]
variable {E F G : Type*}
variable [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
variable [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F]
variable [AddCommGroup G] [Module 𝕜 G] [TopologicalSpace G]
variable (D : E →L[𝕜] F) (L : E →L[𝕜] G)

/-! ### Exactness at the kernel of `D` -/

/-- Exactness of `0 → ker (D.prod L) → ker D → G` at `ker D`: a solution of the linearized
equation satisfies the linearized constraints exactly when the constraint map kills it. -/
theorem ker_domRestrict_eq_comap_ker_prod :
    (L.domRestrict D.ker).ker = (D.prod L).ker.comap D.ker.subtype := by
  ext ⟨x, hx⟩
  simp

/-- The kernel of the extended operator is the kernel of the constraint map on `ker D`. -/
noncomputable def kerProdEquiv :
    (L.domRestrict D.ker).ker ≃ₗ[𝕜] (D.prod L).ker :=
  (LinearEquiv.ofEq _ _ (ker_domRestrict_eq_comap_ker_prod D L)).trans
    (Submodule.comapSubtypeEquivOfLe ((ker_prod D L).trans_le inf_le_left))

/-- The identification of kernels does not move the underlying vector. -/
theorem kerProdEquiv_apply (x : (L.domRestrict D.ker).ker) :
    ((kerProdEquiv D L x : (D.prod L).ker) : E) = ((x : D.ker) : E) :=
  (rfl)

/-- The inverse identification of kernels does not move the underlying vector either. -/
theorem kerProdEquiv_symm_apply (v : (D.prod L).ker) :
    (((kerProdEquiv D L).symm v : D.ker) : E) = v :=
  (rfl)

/-! ### Exactness at the constraint space -/

/-- The map `G → (F × G) ⧸ range (D.prod L)`, `g ↦ [(0, g)]`: it sends a value of the constraints
to the obstruction to realizing it with zero error in the equation. It is the connecting map
`LinearMap.kerToCoker` of the composition `fst ∘ D.prod L = D`, read on `ker fst = G`. -/
noncomputable def constraintToCoker : G →ₗ[𝕜] (F × G) ⧸ (D.prod L).range :=
  (D.prod L : E →ₗ[𝕜] F × G).kerToCoker (LinearMap.fst 𝕜 F G) ∘ₗ
    (LinearMap.inr 𝕜 F G).codRestrict _ fun _ ↦ rfl

/-- The map into the cokernel sends `g` to the class of `(0, g)`. -/
theorem constraintToCoker_apply (g : G) :
    constraintToCoker D L g = Submodule.Quotient.mk ((0 : F), g) :=
  LinearMap.kerToCoker_apply _ _ _

/-- Exactness of `ker D → G → (F × G) ⧸ range (D.prod L)` at `G`: a value `g` of the
constraints has zero obstruction exactly when it is the value of the constraint map at a
solution of the linearized equation. -/
@[simp]
theorem ker_constraintToCoker :
    LinearMap.ker (constraintToCoker D L) = (L.domRestrict D.ker).range := by
  rw [constraintToCoker, LinearMap.ker_comp,
    (LinearMap.exact_kerCompToKer_kerToCoker _ _).linearMap_ker_eq]
  ext g
  -- `coe_prod` would rewrite the operator inside the subtype of `ker (fst ∘ₗ D.prod L)` and
  -- block `coe_kerCompToKer_apply`; for the same reason `codRestrict_apply` does not fire on the
  -- corestriction of `inr`, so it is unfolded instead.
  simp [Subtype.ext_iff, Prod.ext_iff, LinearMap.codRestrict, -ContinuousLinearMap.coe_prod]

/-- Exactness of `ker D → G → (F × G) ⧸ range (D.prod L)` at the middle term. -/
theorem exact_domRestrict_constraintToCoker :
    Function.Exact (L.domRestrict D.ker) (constraintToCoker D L) :=
  LinearMap.exact_iff.mpr (ker_constraintToCoker D L)

/-! ### Exactness at the cokernel of the extended operator -/

/-- The map from the cokernel of the extended operator onto the cokernel of `D`, induced by the
projection `F × G → F`: it forgets the obstructions coming from the constraints. It is
`LinearMap.cokerToCokerComp` for the composition `fst ∘ D.prod L = D`. -/
noncomputable def cokerProdHom : ((F × G) ⧸ (D.prod L).range) →ₗ[𝕜] F ⧸ D.range :=
  (Submodule.quotEquivOfEq _ _ (by rw [coe_prod, LinearMap.fst_prod])).toLinearMap ∘ₗ
    (D.prod L : E →ₗ[𝕜] F × G).cokerToCokerComp (LinearMap.fst 𝕜 F G)

/-- The cokernel map sends the class of `(y, g)` to the class of `y`. -/
theorem cokerProdHom_mk (y : F × G) :
    cokerProdHom D L (Submodule.Quotient.mk y) = Submodule.Quotient.mk y.1 := by
  -- `coe_prod` would rewrite the operator in the type of the quotient class and block
  -- `cokerToCokerComp_mk`.
  simp [cokerProdHom, -ContinuousLinearMap.coe_prod]

/-- Every obstruction for `D` is the image of an obstruction for the extended operator. -/
theorem cokerProdHom_surjective : Function.Surjective (cokerProdHom D L) := by
  rintro ⟨y⟩
  exact ⟨Submodule.Quotient.mk (y, 0), cokerProdHom_mk D L _⟩

/-- Exactness of `G → (F × G) ⧸ range (D.prod L) → F ⧸ range D` at the middle term: the
obstructions for the extended operator that vanish in the cokernel of `D` are exactly those coming
from the constraints. -/
@[simp]
theorem ker_cokerProdHom :
    LinearMap.ker (cokerProdHom D L) = LinearMap.range (constraintToCoker D L) := by
  rw [cokerProdHom, LinearEquiv.ker_comp,
    (LinearMap.exact_kerToCoker_cokerToCokerComp _ _).linearMap_ker_eq, constraintToCoker,
    LinearMap.range_comp_of_range_eq_top]
  -- It remains to see that `inr` maps onto `ker fst`.
  rw [LinearMap.range_eq_top]
  rintro ⟨⟨y, g⟩, hy⟩
  obtain rfl : y = 0 := LinearMap.mem_ker.mp hy
  -- The corestriction of `inr` sends `g` to `(0, g)` by definition.
  exact ⟨g, rfl⟩

/-- Exactness of `G → (F × G) ⧸ range (D.prod L) → F ⧸ range D` at the middle term. -/
theorem exact_constraintToCoker_cokerProdHom :
    Function.Exact (constraintToCoker D L) (cokerProdHom D L) :=
  LinearMap.exact_iff.mpr (ker_cokerProdHom D L)

/-! ### Regularity of the constrained problem -/

/-- **The extended operator is onto exactly when `D` is onto and the constraint map is onto on
the kernel of `D`.** This is the regularity criterion for a problem cut down by finitely many
constraints: a regular solution of the equation satisfies the constraints transversally when the
values of the constraint map on the solutions of the linearized equation fill out `G`. -/
theorem surjective_prod_iff :
    Function.Surjective (D.prod L) ↔
      Function.Surjective D ∧ Function.Surjective (L.domRestrict D.ker) := by
  constructor
  · intro h
    refine ⟨fun y ↦ ?_, fun g ↦ ?_⟩
    · obtain ⟨x, hx⟩ := h (y, 0)
      simp only [prod_apply, Prod.mk.injEq] at hx
      exact ⟨x, hx.1⟩
    · obtain ⟨x, hx⟩ := h (0, g)
      simp only [prod_apply, Prod.mk.injEq] at hx
      refine ⟨⟨x, LinearMap.mem_ker.mpr ?_⟩, ?_⟩
      · rw [coe_coe]
        exact hx.1
      · rw [domRestrict_apply]
        exact hx.2
  · rintro ⟨hD, hL⟩ ⟨y, g⟩
    obtain ⟨x, rfl⟩ := hD y
    obtain ⟨⟨k, hk⟩, hkg⟩ := hL (g - L x)
    rw [LinearMap.mem_ker, coe_coe] at hk
    rw [domRestrict_apply] at hkg
    exact ⟨x + k, by simp [hk, hkg]⟩

/-- If `D` is onto, so is the map from the constraint space onto the cokernel of the extended
operator: every obstruction then comes from the constraints. -/
theorem constraintToCoker_surjective (hD : Function.Surjective D) :
    Function.Surjective (constraintToCoker D L) := by
  intro z
  have hz : z ∈ LinearMap.ker (cokerProdHom D L) := by
    have : Subsingleton (F ⧸ D.range) := by
      rw [LinearMap.range_eq_top.mpr hD]
      infer_instance
    exact LinearMap.mem_ker.mpr (Subsingleton.elim _ _)
  rw [ker_cokerProdHom] at hz
  exact LinearMap.mem_range.mp hz

/-- **For an onto `D`, the cokernel of the extended operator is the cokernel of the constraint
map on `ker D`**, identified by `g ↦ [(0, g)]`. It is the obstruction space of the constrained
problem at a regular solution of the unconstrained one. -/
noncomputable def constraintCokerEquiv (hD : Function.Surjective D) :
    (G ⧸ (L.domRestrict D.ker).range) ≃ₗ[𝕜] (F × G) ⧸ (D.prod L).range :=
  (Submodule.quotEquivOfEq _ _ (ker_constraintToCoker D L).symm).trans
    (LinearMap.quotKerEquivOfSurjective _ (constraintToCoker_surjective D L hD))

/-- The cokernel equivalence sends the class of `g` to the class of `(0, g)`. -/
theorem constraintCokerEquiv_mk (hD : Function.Surjective D) (g : G) :
    constraintCokerEquiv D L hD (Submodule.Quotient.mk g) = Submodule.Quotient.mk ((0 : F), g) :=
  constraintToCoker_apply D L g

/-! ### Incidence constraints -/

/-- **Transversality to an incidence condition.** Constraining the values of `ev` to a subspace
`N` gives the extended operator `x ↦ (D x, [ev x])` into `F × (G ⧸ N)`. It is onto exactly when
`D` is onto and the values of `ev` on the solutions of the linearized equation are transverse to
`N`. -/
theorem surjective_prod_mkQL_comp_iff (ev : E →L[𝕜] G) (N : Submodule 𝕜 G) :
    Function.Surjective (D.prod (N.mkQL ∘L ev)) ↔
      Function.Surjective D ∧ D.ker.map (ev : E →ₗ[𝕜] G) ⊔ N = ⊤ := by
  have hrange : ((N.mkQL ∘L ev).domRestrict D.ker).range =
      (D.ker.map (ev : E →ₗ[𝕜] G)).map N.mkQ := by
    ext z
    simp
  rw [surjective_prod_iff, ← coe_coe ((N.mkQL ∘L ev).domRestrict D.ker),
    ← LinearMap.range_eq_top, hrange, Submodule.map_mkQ_eq_top, sup_comm]

end Ring

/-! ### Dimensions -/

section DivisionRing

variable {𝕜 : Type*} [DivisionRing 𝕜]
variable {E F G : Type*}
variable [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
variable [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F]
variable [AddCommGroup G] [Module 𝕜 G] [TopologicalSpace G]
variable (D : E →L[𝕜] F) (L : E →L[𝕜] G)

/-- The constraints cut the kernel of `D` down by the rank of the constraint map on it. -/
theorem finrank_ker_prod_add_finrank_range_domRestrict [FiniteDimensional 𝕜 D.ker] :
    finrank 𝕜 (D.prod L).ker + finrank 𝕜 ((L.domRestrict D.ker).range) =
      finrank 𝕜 D.ker := by
  have h := (L.domRestrict D.ker : D.ker →ₗ[𝕜] G).finrank_range_add_finrank_ker
  rw [(kerProdEquiv D L).finrank_eq] at h
  omega

/-- The cokernel of the extended operator is finite dimensional when the cokernel of `D` and the
constraint space are. -/
theorem finiteDimensional_quotient_range_prod [FiniteDimensional 𝕜 (F ⧸ D.range)]
    [FiniteDimensional 𝕜 G] : FiniteDimensional 𝕜 ((F × G) ⧸ (D.prod L).range) :=
  (exact_constraintToCoker_cokerProdHom D L).moduleFinite

/-- The constraints enlarge the cokernel of `D` by the corank of the constraint map on `ker D`. -/
theorem finrank_quotient_range_prod_add_finrank_range_domRestrict
    [FiniteDimensional 𝕜 (F ⧸ D.range)] [FiniteDimensional 𝕜 G] :
    finrank 𝕜 ((F × G) ⧸ (D.prod L).range) +
        finrank 𝕜 ((L.domRestrict D.ker).range) =
      finrank 𝕜 (F ⧸ D.range) + finrank 𝕜 G := by
  have := finiteDimensional_quotient_range_prod D L
  have hcoker := LinearMap.finrank_eq_finrank_range_add_finrank_range_of_exact _ _
    (exact_constraintToCoker_cokerProdHom D L)
  rw [LinearMap.range_eq_top.mpr (cokerProdHom_surjective D L), finrank_top] at hcoker
  have hconstr := (constraintToCoker D L).finrank_range_add_finrank_ker
  rw [ker_constraintToCoker] at hconstr
  omega

/-- **Imposing finitely many constraints lowers the index by their number**, provided the kernel
and cokernel of `D` are finite dimensional. Neither Fredholmness nor surjectivity of the extended
operator is required. -/
theorem index_prod [FiniteDimensional 𝕜 D.ker] [FiniteDimensional 𝕜 (F ⧸ D.range)]
    [FiniteDimensional 𝕜 G] :
    (D.prod L).index = D.index - finrank 𝕜 G := by
  have hker := finrank_ker_prod_add_finrank_range_domRestrict D L
  have hcoker := finrank_quotient_range_prod_add_finrank_range_domRestrict D L
  rw [index_eq_finrank_sub, index_eq_finrank_sub]
  omega

/-- For an onto `D`, the extended operator is onto exactly when its kernel has the expected
dimension `dim ker D - dim G`. -/
theorem surjective_prod_iff_finrank_ker_add [FiniteDimensional 𝕜 D.ker] [FiniteDimensional 𝕜 G]
    (hD : Function.Surjective D) :
    Function.Surjective (D.prod L) ↔ finrank 𝕜 (D.prod L).ker + finrank 𝕜 G = finrank 𝕜 D.ker := by
  have h := finrank_ker_prod_add_finrank_range_domRestrict D L
  rw [surjective_prod_iff, and_iff_right hD, ← coe_coe (L.domRestrict D.ker),
    ← LinearMap.range_eq_top]
  constructor
  · intro htop
    rw [htop, finrank_top] at h
    omega
  · intro hk
    exact Submodule.eq_top_of_finrank_eq (by omega)

end DivisionRing

/-! ### Fredholmness -/

section Fredholm

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
variable {E F G : Type*}
variable [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [ContinuousSMul 𝕜 E] [T2Space E]
variable [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F] [IsTopologicalAddGroup F]
  [ContinuousSMul 𝕜 F] [T2Space F]
variable [AddCommGroup G] [Module 𝕜 G] [TopologicalSpace G] [IsTopologicalAddGroup G]
  [ContinuousSMul 𝕜 G] [T2Space G] [FiniteDimensional 𝕜 G]

/-- **An operator extended by finitely many constraints is Fredholm exactly when the operator
is.** The extended operator differs from `x ↦ (D x, 0)` by the finite-rank operator
`x ↦ (0, L x)`. -/
@[simp]
theorem isFredholm_prod_iff {D : E →L[𝕜] F} {L : E →L[𝕜] G} :
    IsFredholm (D.prod L) ↔ IsFredholm D := by
  have hsplit : D.prod L = (inl 𝕜 F G).comp D + (inr 𝕜 F G).comp L := by
    ext x : 1
    simp
  have hfin (M : E →L[𝕜] G) : ((inr 𝕜 F G).comp M).toLinearMap.HasFiniteRange :=
    LinearMap.HasFiniteRange.of_finite_dom.comp_right _
  rw [hsplit, ← (isFredholm_inl (K := 𝕜) F G).comp_iff_right (f := D)]
  exact ⟨fun h ↦ by simpa using h.add_hasFiniteRange (hfin (-L)),
    fun h ↦ h.add_hasFiniteRange (hfin L)⟩

end Fredholm

end ContinuousLinearMap
