/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Instances.AddCircle.Real
public import TauCeti.Algebra.Module.ZLattice.Rank
import TauCeti.LinearAlgebra.Basis.SumExtend

/-!
# Quotients by discrete subgroups are cylinders `Tʳ × ℝⁿ⁻ʳ`

Let `L` be a discrete subgroup of a finite-dimensional real normed space `E` of dimension `n`.
It need not span `E`. Then `L` is a free abelian group of some rank `r`, a `ℤ`-basis of `L` is
linearly independent over `ℝ`, and completing it to a real basis of `E` gives coordinates in which
`L` is the standard lattice `ℤʳ × 0`. Reducing the first `r` coordinates modulo one identifies
the quotient with a cylinder:

`E ⧸ L ≃ₜ+ (ℝ / ℤ)ʳ × ℝⁿ⁻ʳ`.

For a full lattice (`r = n`) this is the torus of `Module.Basis.quotientLatticeEquiv`. Unlike that
case, the quotient need not be compact, so the inverse map is shown continuous by openness of the
coordinate map rather than by compactness.

## Main definitions

* `Module.Basis.cylinderCoordinates B`: for a real basis `B` of `E` indexed by `ι ⊕ κ`, the
  continuous homomorphism `E → (ℝ / ℤ)^ι × ℝ^κ` taking the `ι`-coordinates modulo one and keeping
  the `κ`-coordinates.
* `Module.Basis.quotientCylinderEquiv B hL`: if `L` is the integer span of the vectors `B (inl i)`,
  the induced isomorphism of topological groups `E ⧸ L ≃ₜ+ (ℝ / ℤ)^ι × ℝ^κ`.

## Main results

* `Module.Basis.ker_cylinderCoordinates`: the kernel of the cylinder coordinates is the integer
  span of the vectors `B (inl i)`.
* `AddSubgroup.exists_basis_span_range_comp_inl_eq`: a discrete subgroup of rank `r` is the integer
  span of the first `r` vectors of a real basis of `E`.
* `AddSubgroup.nonempty_quotient_continuousAddEquiv_unitAddTorus_prod`: the quotient by a discrete
  subgroup of rank `r` is isomorphic, as a topological group, to `(ℝ / ℤ)ʳ × ℝⁿ⁻ʳ`.

## References

* N. Bourbaki, *General Topology*, Chapter VII, § 1, no. 2, Theorem 2 (closed subgroups of `ℝⁿ`,
  in particular discrete ones, and the corresponding quotients).
* V. I. Arnold, *Mathematical Methods of Classical Mechanics*, 2nd ed., Graduate Texts in
  Mathematics 60, Springer, 1989, Section 49 (discrete subgroups of `ℝⁿ` and the quotients
  `Tʳ × ℝⁿ⁻ʳ`).
-/

public section

noncomputable section

open Module Submodule

namespace Module.Basis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {ι κ : Type*} (B : Basis (ι ⊕ κ) ℝ E)

/-- Cylinder coordinates for a real basis indexed by `ι ⊕ κ`: the `ι`-coordinates reduced modulo
one, and the `κ`-coordinates. -/
def cylinderCoordinates : E →ₜ+ UnitAddTorus ι × (κ → ℝ) where
  toFun x := (fun i ↦ (B.repr x (.inl i) : UnitAddCircle), fun k ↦ B.repr x (.inr k))
  map_zero' := by ext <;> simp
  map_add' x y := by ext <;> simp
  continuous_toFun := by
    refine .prodMk (continuous_pi fun i ↦ ?_) (continuous_pi fun k ↦ ?_)
    · exact (AddCircle.continuous_mk' (1 : ℝ)).comp
        (B.coord (.inl i)).continuous_of_finiteDimensional
    · exact (B.coord (.inr k)).continuous_of_finiteDimensional

@[simp]
theorem cylinderCoordinates_apply_fst (x : E) (i : ι) :
    (B.cylinderCoordinates x).1 i = (B.repr x (.inl i) : UnitAddCircle) :=
  (rfl)

@[simp]
theorem cylinderCoordinates_apply_snd (x : E) (k : κ) :
    (B.cylinderCoordinates x).2 k = B.repr x (.inr k) :=
  (rfl)

/-- The vectors with integral `ι`-coordinates and vanishing `κ`-coordinates are exactly the
integer combinations of the vectors `B (inl i)`. -/
@[simp]
theorem ker_cylinderCoordinates :
    (B.cylinderCoordinates : E →+ UnitAddTorus ι × (κ → ℝ)).ker =
      (span ℤ (Set.range (B ∘ Sum.inl))).toAddSubgroup := by
  have := Module.Finite.finite_basis B
  have := Finite.sum_left κ (α := ι)
  have := Finite.sum_right ι (β := κ)
  have := Fintype.ofFinite ι
  have := Fintype.ofFinite κ
  classical
  ext x
  rw [AddMonoidHom.mem_ker, Submodule.mem_toAddSubgroup]
  constructor
  · intro hx
    have h₁ (i : ι) : ∃ n : ℤ, (n : ℝ) = B.repr x (.inl i) := by
      obtain ⟨n, hn⟩ := AddSubgroup.mem_zmultiples_iff.mp <| by
        simpa using congrFun (congrArg Prod.fst hx) i
      exact ⟨n, by simpa using hn⟩
    have h₂ (k : κ) : B.repr x (.inr k) = 0 := congrFun (congrArg Prod.snd hx) k
    choose n hn using h₁
    rw [← B.sum_repr x, Fintype.sum_sum_type]
    simp only [h₂, zero_smul, Finset.sum_const_zero, add_zero, ← hn]
    exact Submodule.sum_mem _ fun i _ ↦ by
      rw [Int.cast_smul_eq_zsmul]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  · intro hx
    have hle : span ℤ (Set.range (B ∘ Sum.inl)) ≤
        (B.cylinderCoordinates : E →+ UnitAddTorus ι × (κ → ℝ)).ker.toIntSubmodule := by
      rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      rw [AddSubgroup.coe_toIntSubmodule, SetLike.mem_coe, AddMonoidHom.mem_ker,
        AddMonoidHom.coe_ofClass, Function.comp_apply]
      ext j
      · rw [cylinderCoordinates_apply_fst, repr_self, Finsupp.single_apply]
        split_ifs <;> simp
      · simp
    exact hle hx

/-- Every point of the cylinder has cylinder coordinates. -/
theorem cylinderCoordinates_surjective : Function.Surjective B.cylinderCoordinates := by
  have := Module.Finite.finite_basis B
  rintro ⟨t, y⟩
  choose x hx using fun i ↦ QuotientAddGroup.mk_surjective (t i)
  refine ⟨B.equivFun.symm (Sum.elim x y), ?_⟩
  ext i
  · rw [cylinderCoordinates_apply_fst, ← B.equivFun_apply, LinearEquiv.apply_symm_apply]
    exact hx i
  · rw [cylinderCoordinates_apply_snd, ← B.equivFun_apply, LinearEquiv.apply_symm_apply]
    rfl

/-- Cylinder coordinates form an open map. -/
theorem isOpenMap_cylinderCoordinates : IsOpenMap B.cylinderCoordinates := by
  have := Module.Finite.finite_basis B
  -- The real coordinates are a linear homeomorphism `E ≃ ℝ^ι × ℝ^κ`; reduction modulo one is an
  -- open quotient map on each `ι`-coordinate.
  let c := (B.equivFun.trans (LinearEquiv.sumArrowLequivProdArrow ι κ ℝ ℝ)).toContinuousLinearEquiv
  have hc : ⇑B.cylinderCoordinates =
      Prod.map (Pi.map fun _ ↦ ((↑) : ℝ → UnitAddCircle)) id ∘ c := by
    ext x <;> simp [c, LinearEquiv.sumArrowLequivProdArrow]
  rw [hc]
  exact (IsOpenMap.prodMap (.piMap (fun _ ↦ QuotientAddGroup.isOpenMap_coe)
    (.of_forall fun _ ↦ QuotientAddGroup.mk_surjective)) IsOpenMap.id).comp
    c.toHomeomorph.isOpenMap

variable {L : AddSubgroup E} (hL : L = (span ℤ (Set.range (B ∘ Sum.inl))).toAddSubgroup)

/-- If `L` is the integer span of the vectors `B (inl i)`, cylinder coordinates identify `E ⧸ L`
with `(ℝ / ℤ)^ι × ℝ^κ` as topological groups. -/
def quotientCylinderEquiv : (E ⧸ L) ≃ₜ+ UnitAddTorus ι × (κ → ℝ) :=
  let e := QuotientAddGroup.liftEquiv L B.cylinderCoordinates_surjective
    (hL.trans B.ker_cylinderCoordinates.symm)
  have he : ⇑e ∘ QuotientAddGroup.mk = B.cylinderCoordinates :=
    funext fun x ↦ QuotientAddGroup.liftEquiv_mk L _ _ x
  have hc : Continuous e :=
    (QuotientAddGroup.isQuotientMap_mk L).continuous_iff.mpr (he ▸ map_continuous _)
  let h := e.toEquiv.toHomeomorphOfContinuousOpen hc <|
    IsOpenMap.of_comp QuotientAddGroup.continuous_mk QuotientAddGroup.mk_surjective <|
      he ▸ B.isOpenMap_cylinderCoordinates
  { e with
    continuous_toFun := hc
    continuous_invFun := h.continuous_symm }

@[simp]
theorem quotientCylinderEquiv_apply_mk (x : E) :
    B.quotientCylinderEquiv hL (QuotientAddGroup.mk x) = B.cylinderCoordinates x :=
  QuotientAddGroup.liftEquiv_mk L B.cylinderCoordinates_surjective
    (hL.trans B.ker_cylinderCoordinates.symm) x

/-- The inverse cylinder coordinates send reduced coordinates `x` and coordinates `y` to the class
of the vector with real coordinates `x` and `y` in the basis `B`. -/
@[simp]
theorem quotientCylinderEquiv_symm_apply [Finite ι] [Finite κ] (x : ι → ℝ) (y : κ → ℝ) :
    (B.quotientCylinderEquiv hL).symm (fun i ↦ (x i : UnitAddCircle), y) =
      QuotientAddGroup.mk (B.equivFun.symm (Sum.elim x y)) := by
  apply (B.quotientCylinderEquiv hL).injective
  rw [ContinuousAddEquiv.apply_symm_apply, quotientCylinderEquiv_apply_mk]
  ext i
  · rw [cylinderCoordinates_apply_fst, ← B.equivFun_apply, LinearEquiv.apply_symm_apply]
    rfl
  · rw [cylinderCoordinates_apply_snd, ← B.equivFun_apply, LinearEquiv.apply_symm_apply]
    rfl

end Module.Basis

namespace AddSubgroup

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  (L : AddSubgroup E) [DiscreteTopology L]

/-- **Adapted bases of discrete subgroups.** A discrete subgroup `L` of rank `r` of a real space of
dimension `n` is the integer span of the first `r` vectors of a real basis indexed by
`Fin r ⊕ Fin (n - r)`. -/
theorem exists_basis_span_range_comp_inl_eq :
    ∃ B : Basis (Fin (finrank ℤ L.toIntSubmodule) ⊕
        Fin (finrank ℝ E - finrank ℤ L.toIntSubmodule)) ℝ E,
      (span ℤ (Set.range (B ∘ Sum.inl))).toAddSubgroup = L := by
  set r := finrank ℤ L.toIntSubmodule
  have : DiscreteTopology L.toIntSubmodule := ‹DiscreteTopology L›
  -- A `ℤ`-basis of `L`, read in `E`.
  let b := Module.finBasis ℤ L.toIntSubmodule
  let v : Fin r → E := fun i ↦ b i
  have hspan : span ℤ (Set.range v) = L.toIntSubmodule := by
    have := congrArg (Submodule.map L.toIntSubmodule.subtype) b.span_eq
    rwa [Submodule.map_span, ← Set.range_comp, Submodule.map_top, Submodule.range_subtype] at this
  -- It is linearly independent over `ℝ`, since the real and integer ranks of `L` agree.
  have hv : LinearIndependent ℝ v := by
    rw [linearIndependent_iff_card_eq_finrank_span, Fintype.card_fin, Set.finrank,
      ← Submodule.span_span_of_tower ℤ, hspan]
    exact (setFinrank_real_eq_finrank_int L.toIntSubmodule).symm
  -- Complete it to a real basis and count the new vectors.
  let B₀ := Basis.sumExtend hv
  have := Module.Finite.finite_basis B₀
  have : Finite (Basis.sumExtendIndex hv) :=
    .of_injective (Sum.inr : _ → Fin r ⊕ _) Sum.inr_injective
  have hcard : Nat.card (Basis.sumExtendIndex hv) = finrank ℝ E - r := by
    rw [Module.finrank_eq_nat_card_basis B₀, Nat.card_sum, Nat.card_fin]
    omega
  let e := (Finite.equivFin (Basis.sumExtendIndex hv)).trans (finCongr hcard)
  refine ⟨B₀.reindex (Equiv.sumCongr (Equiv.refl _) e), ?_⟩
  have hB : (B₀.reindex (Equiv.sumCongr (Equiv.refl _) e)) ∘ Sum.inl = v := by
    ext i
    simp [B₀]
  rw [hB, hspan, AddSubgroup.toIntSubmodule_toAddSubgroup]

/-- **The quotient by a discrete subgroup is a cylinder.** If `L` is a discrete subgroup of rank `r`
of a real space `E` of dimension `n`, then `E ⧸ L` is isomorphic as a topological group to
`(ℝ / ℤ)ʳ × ℝⁿ⁻ʳ`. -/
theorem nonempty_quotient_continuousAddEquiv_unitAddTorus_prod :
    Nonempty ((E ⧸ L) ≃ₜ+ UnitAddTorus (Fin (finrank ℤ L.toIntSubmodule)) ×
      (Fin (finrank ℝ E - finrank ℤ L.toIntSubmodule) → ℝ)) :=
  let ⟨B, hB⟩ := L.exists_basis_span_range_comp_inl_eq
  ⟨B.quotientCylinderEquiv hB.symm⟩

end AddSubgroup
