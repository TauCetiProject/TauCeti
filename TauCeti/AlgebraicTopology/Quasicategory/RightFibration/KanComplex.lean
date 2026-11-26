/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Quasicategory.OuterHorn.Parametrized
public import TauCeti.AlgebraicTopology.SimplicialSet.TrivialFibration.Fiber
public import TauCeti.AlgebraicTopology.SimplicialSet.WeakHomotopyEquivalence

/-!
# Right and left fibrations over Kan complexes

This file proves the two basic comparisons between right fibrations and Kan fibrations
(HTT Section 2.1.3), and their duals for left fibrations.

A right fibration over a Kan complex is a Kan fibration
(`SSet.RightFibration.fibration_of_kanComplex`, HTT Lemma 2.1.3.3). The horns `Λ[n, i]` with
`0 < i` lift by definition. The source of a right fibration `p : X ⟶ Y` over a quasicategory is a
quasicategory, and `p` reflects equivalences. Every edge of a Kan complex is an equivalence, so
every edge of `X` is one too. Hence the horns `Λ[n + 2, 0]` lift by the relative form of Joyal's
special outer horn theorem, `SSet.InnerFibration.hasLift_horn_zero`, and the horn `Λ[1, 0]` lifts
because right fibrations lift equivalences with prescribed source. In particular, the fibres of a
right fibration, which lie over a point, are Kan complexes
(`SSet.fiber.kanComplex_of_rightFibration`).

A right fibration is a trivial fibration exactly when its fibres are weakly contractible
(`SSet.RightFibration.rlp_monomorphisms_iff_isWeaklyContractible_fiber`, HTT Lemma 2.1.3.4). The
proof adapts the one for Kan fibrations,
`SSet.rlp_monomorphisms_iff_fibration_and_isWeaklyContractible_fiber`. To lift a map `∂Δ[n] ⟶ X`
over a simplex `b : Δ[n] ⟶ Y`, contract `Δ[n]` onto its initial vertex.

* Over the boundary, lift the contraction backwards, which right fibrations allow; it ends in the
  fibre over the initial vertex of `b`.
* This fibre is a weakly contractible Kan complex, so the end extends to `Δ[n]`.
* Lift the contraction forwards over `Δ[n]`, extending these two lifts. For a right fibration,
  this lifting problem along `(Δ[n] ⊗ {0}) ∪ (∂Δ[n] ⊗ Δ[1]) ⟶ Δ[n] ⊗ Δ[1]` is solved in the
  pullback of `p` along `b`, a quasicategory. Moss's pairing for the prism attaches inner horns
  and horns `Λ[d + 1, 0]` with initial edge `{0} ⊗ Δ[1]`
  (`SSet.prodStdSimplex.exists_ext_unionProd_horn_zero`). This edge lies over a degenerate edge of
  `Δ[n]`, so it is an equivalence, and Joyal's theorem fills these horns.

Both results pass to left fibrations along the opposite functor `SSet.opFunctor`, which exchanges
left and right fibrations (`SSet.leftFibration_opFunctor_map_iff`) and preserves and reflects Kan
fibrations, Kan complexes, trivial fibrations and weak contractibility.

## Main results

* `SSet.RightFibration.fibration_of_kanComplex`, `SSet.LeftFibration.fibration_of_kanComplex`: a
  right or left fibration over a Kan complex is a Kan fibration.
* `SSet.fiber.kanComplex_of_rightFibration`, `SSet.fiber.kanComplex_of_leftFibration`: the fibres
  of right and left fibrations are Kan complexes.
* `SSet.RightFibration.rlp_monomorphisms_iff_isWeaklyContractible_fiber`,
  `SSet.LeftFibration.rlp_monomorphisms_iff_isWeaklyContractible_fiber`: a right or left fibration
  is a trivial fibration exactly when its fibres are weakly contractible.

## References

* J. Lurie, *Higher Topos Theory*, Lemmas 2.1.3.3 and 2.1.3.4.
* J. Lurie, *Kerodon*, Theorem 4.4.2.6.
* S. Moss, *Another approach to the Kan-Quillen model structure*, J. Homotopy Relat. Struct. 15
  (2020).
-/

public section

universe u

open CategoryTheory Limits MorphismProperty MonoidalCategory CartesianMonoidalCategory
  HomotopicalAlgebra Simplicial

namespace SSet

open modelCategoryQuillen Edge

variable {X Y : SSet.{u}}

namespace RightFibration

/-- **A right fibration over a Kan complex is a Kan fibration** (HTT Lemma 2.1.3.3). -/
theorem fibration_of_kanComplex (p : X ⟶ Y) [RightFibration p] [KanComplex Y] :
    Fibration p := by
  have := quasicategory_of_innerFibration p
  rw [fibration_iff, rlp_J_iff]
  intro n i
  by_cases hi : i = 0
  · subst hi
    obtain _ | n := n
    · exact ⟨fun sq ↦ hasLift_of_isEquivalence p sq (isEquivalence_of_kanComplex _)⟩
    · exact ⟨fun sq ↦ InnerFibration.hasLift_horn_zero p sq
        ((isEquivalence_map_iff_of_rightFibration p _).1 (isEquivalence_of_kanComplex _))⟩
  · exact (rightFibration_iff_hasLiftingProperty p).1 inferInstance i (Fin.pos_iff_ne_zero.2 hi)

end RightFibration

/-- The fibres of a right fibration are Kan complexes. -/
instance fiber.kanComplex_of_rightFibration (q : X ⟶ Y) [RightFibration q] (y : Y _⦋0⦌) :
    KanComplex (fiber q y) := by
  have := kanComplex_of_isTerminal (Subcomplex.isTerminalOfSimplex y)
  have := RightFibration.fibration_of_kanComplex ((Subcomplex.ofSimplex y).fromPreimage q)
  -- `fiber q y` is the source of the restriction of `q` over `ofSimplex y`.
  rw [fiber_eq_preimage]
  exact isFibrant_of_fibration ((Subcomplex.ofSimplex y).fromPreimage q)

section prism

variable {C : SSet.{u}} {n : ℕ}

/-- **Covering homotopies over a boundary, for right fibrations.** Let `p : X ⟶ Y` be a right
fibration and `H = h ≫ b : Δ[n + 1] ⊗ Δ[1] ⟶ Y` a homotopy through a standard simplex `Δ[k]` which
is constant on the vertical edge `{0} ⊗ Δ[1]`. A lift `g` of its start and a lift `L` of its
restriction to `∂Δ[n + 1] ⊗ Δ[1]`, agreeing on `∂Δ[n + 1] ⊗ {0}`, extend to a lift of `H`. The
proof extends in the pullback of `p` along `b`, a quasicategory in which the lifted vertical edge is
an equivalence, and uses that maps to `Δ[k]` are determined by their values on vertices, all of
which lie in `∂Δ[n + 1] ⊗ Δ[1]`. -/
private lemma exists_lift_cylinder_boundary (p : X ⟶ Y) [RightFibration p] {k : ℕ}
    (h : Δ[n + 1] ⊗ Δ[1] ⟶ Δ[k]) (b : Δ[k] ⟶ Y) (g : Δ[n + 1] ⟶ X)
    (L : (∂Δ[n + 1] : SSet.{u}) ⊗ Δ[1] ⟶ X) (hg : g ≫ p = ι₀ ≫ h ≫ b)
    (hL : L ≫ p = ∂Δ[n + 1].ι ▷ Δ[1] ≫ h ≫ b) (hgL : ∂Δ[n + 1].ι ≫ g = ι₀ ≫ L)
    (h0 : (ι₀ ≫ h).app _ (stdSimplex.obj₀Equiv.symm 0) =
      (ι₁ ≫ h).app _ (stdSimplex.obj₀Equiv.symm 0)) :
    ∃ L' : Δ[n + 1] ⊗ Δ[1] ⟶ X, ι₀ ≫ L' = g ∧ ∂Δ[n + 1].ι ▷ Δ[1] ≫ L' = L ∧ L' ≫ p = h ≫ b := by
  have : RightFibration (pullback.snd p b) :=
    RightFibration.of_isPullback (IsPullback.of_hasPullback p b)
  have := quasicategory_of_innerFibration (pullback.snd p b)
  let g' := pullback.lift g (ι₀ ≫ h) hg
  let L₁ := pullback.lift L (∂Δ[n + 1].ι ▷ Δ[1] ≫ h) hL
  have hgL' : ∂Δ[n + 1].ι ≫ g' = ι₀ ≫ L₁ :=
    pullback.hom_ext (by simp [g', L₁, hgL]) (by simp [g', L₁])
  -- The vertical edge `{0} ⊗ Δ[1]` lifts to an edge of the pullback over an edge of `Δ[k]` with
  -- equal endpoints, an equivalence; right fibrations reflect equivalences.
  have hL₁ : (Edge.mk' (L₁.app _
      (boundary.edgeZero n, stdSimplex.edge 1 0 1 (Fin.zero_le _)))).IsEquivalence := by
    refine (isEquivalence_map_iff_of_rightFibration (pullback.snd p b) _).1 ?_
    -- The vertical edge at `0`, an edge of `Δ[n + 1] ⊗ Δ[1]`, is sent by `h` to an edge of
    -- `Δ[k]` from a vertex to itself, which is the identity edge.
    let e₀ : Edge (ι₀.app _ (stdSimplex.obj₀Equiv.symm 0) : (Δ[n + 1] ⊗ Δ[1] : SSet.{u}) _⦋0⦌)
        (ι₁.app _ (stdSimplex.obj₀Equiv.symm 0)) :=
      Edge.mk (stdSimplex.const (n + 1) 0 _, stdSimplex.edge 1 0 1 (Fin.zero_le _))
        (Prod.ext (stdSimplex.ext _ _ fun i ↦ by fin_cases i; rfl)
          (stdSimplex.ext _ _ fun i ↦ by fin_cases i; rfl))
        (Prod.ext (stdSimplex.ext _ _ fun i ↦ by fin_cases i; rfl)
          (stdSimplex.ext _ _ fun i ↦ by fin_cases i; rfl))
    have he : (e₀.map h).IsEquivalence := by
      rw [← isEquivalence_ofEq_iff rfl h0.symm,
        Subsingleton.elim ((e₀.map h).ofEq rfl h0.symm) (Edge.id _)]
      exact isEquivalence_id _
    refine (isEquivalence_iff_of_edge_eq ?_).1 he
    rw [map_edge, map_edge, mk'_edge]
    have he₀ : (∂Δ[n + 1].ι ▷ Δ[1]).app _
        (boundary.edgeZero n, stdSimplex.edge 1 0 1 (Fin.zero_le _)) = e₀.edge :=
      Prod.ext (boundary.edgeZero_val n) rfl
    exact (congrArg (h.app _) he₀).symm.trans
      (congrArg (fun f ↦ f.app _ (boundary.edgeZero n, stdSimplex.edge 1 0 1 (Fin.zero_le _)))
        (pullback.lift_snd L (∂Δ[n + 1].ι ▷ Δ[1] ≫ h) hL)).symm
  obtain ⟨L', hL'₀, hL'₁⟩ := Quasicategory.exists_ext_cylinder_boundary g' L₁ hgL' hL₁
  refine ⟨L' ≫ pullback.fst _ _, by rw [reassoc_of% hL'₀, pullback.lift_fst],
    by rw [reassoc_of% hL'₁, pullback.lift_fst], ?_⟩
  rw [Category.assoc, pullback.condition, ← Category.assoc]
  congr 1
  -- Every vertex of `Δ[n + 1] ⊗ Δ[1]` lies in `∂Δ[n + 1] ⊗ Δ[1]`, where `L'` lies over `h`.
  refine stdSimplex.hom_ext fun z ↦ ?_
  have hz : ∂Δ[n + 1].ι ▷ Δ[1] ≫ L' ≫ pullback.snd _ _ = ∂Δ[n + 1].ι ▷ Δ[1] ≫ h := by
    rw [reassoc_of% hL'₁, pullback.lift_snd]
  exact congrArg (fun f ↦ f.app _ ((⟨z.1, by simp [boundary_obj_eq_univ]⟩ :
    (∂Δ[n + 1] : SSet.{u}) _⦋0⦌), z.2)) hz

end prism

namespace RightFibration

/-- **A right fibration is a trivial fibration exactly when its fibres are weakly contractible**
(HTT Lemma 2.1.3.4). For a Kan fibration this is
`SSet.rlp_monomorphisms_iff_fibration_and_isWeaklyContractible_fiber`; the fibres of a right
fibration are Kan complexes (`SSet.fiber.kanComplex_of_rightFibration`). -/
theorem rlp_monomorphisms_iff_isWeaklyContractible_fiber (p : X ⟶ Y) [RightFibration p] :
    (monomorphisms SSet.{u}).rlp p ↔ ∀ y : Y _⦋0⦌, IsWeaklyContractible (fiber p y : SSet.{u}) := by
  refine ⟨fun hp ↦ (rlp_monomorphisms_iff_fibration_and_isWeaklyContractible_fiber.1 hp).2,
    fun hp ↦ ?_⟩
  -- The fibre over `y` is a contractible Kan complex, so maps to it extend along monomorphisms.
  have hF (y : Y _⦋0⦌) := (rlp_monomorphisms_iff_kanComplex_and_isWeaklyContractible_of_isTerminal
    stdSimplex.isTerminalObj₀ (stdSimplex.isTerminalObj₀.from (fiber p y : SSet.{u}))).2
      ⟨inferInstance, hp y⟩
  rw [SSet.rlp_monomorphisms]
  rintro _ _ _ ⟨_ | n⟩
  · -- Over a vertex `y`, choose a vertex of the nonempty fibre over `y`.
    refine ⟨fun {a b} sq ↦ ?_⟩
    obtain ⟨x⟩ := IsWeaklyContractible.nonempty (K := (fiber p (yonedaEquiv b) : SSet.{u}))
    have hx := congrArg (fun f ↦ f.app _ x) (fiber.ι_comp p (yonedaEquiv b))
    refine ⟨⟨⟨yonedaEquiv.symm ((fiber p (yonedaEquiv b)).ι.app _ x), boundary.hom_ext₀,
      yonedaEquiv.injective ?_⟩⟩⟩
    rw [yonedaEquiv_comp, Equiv.apply_symm_apply]
    exact hx.trans (by simp)
  · refine ⟨fun {a b} sq ↦ ?_⟩
    let C := stdSimplex.contraction.{u} (n + 1)
    let y := b.app _ (stdSimplex.obj₀Equiv.symm 0)
    have hC₀ : ι₀ ≫ C.h ≫ b = const y := by rw [C.h₀_assoc, const_comp]
    -- Over the boundary, lift the contraction backwards from `a`, ending in the fibre over `y`.
    have := (rightAnodyneExtensions_ι₁ (∂Δ[n + 1] : SSet.{u})).hasLiftingProperty p
    have sq₁ : CommSq a ι₁ p (∂Δ[n + 1].ι ▷ Δ[1] ≫ C.h ≫ b) :=
      ⟨by rw [ι₁_comp_assoc, C.h₁_assoc, Category.id_comp, sq.w]⟩
    let L₁ := sq₁.lift
    have hL₁ : (ι₀ ≫ L₁) ≫ p = const y := by
      rw [Category.assoc, sq₁.fac_right, ι₀_comp_assoc, hC₀, comp_const]
    -- The end of `L₁` extends to `Δ[n + 1]` in the fibre over `y`.
    have := hF y _ (monomorphisms.infer_property ∂Δ[n + 1].ι)
    have sqF : CommSq (Subcomplex.lift (ι₀ ≫ L₁) ((range_le_fiber_iff _ p y).2 hL₁))
        ∂Δ[n + 1].ι (stdSimplex.isTerminalObj₀.from (fiber p y : SSet.{u}))
        (stdSimplex.isTerminalObj₀.from _) :=
      ⟨stdSimplex.isTerminalObj₀.hom_ext _ _⟩
    let g := sqF.lift ≫ (fiber p y).ι
    have hg : ∂Δ[n + 1].ι ≫ g = ι₀ ≫ L₁ := by
      simp only [g, sqF.fac_left_assoc, Subcomplex.lift_ι]
    have hgp : g ≫ p = ι₀ ≫ C.h ≫ b := by
      have := (range_le_fiber_iff (fiber p y).ι p y).1 (by simp)
      rw [hC₀]
      simp [g, this]
    -- Lift the contraction forwards over `Δ[n + 1]`, prescribed by `g` at the start and by `L₁`
    -- on the boundary: its vertical edge at `0` is constant.
    obtain ⟨L, -, hL, hLp⟩ := exists_lift_cylinder_boundary p C.h b g L₁ hgp sq₁.fac_right
      hg (by rw [C.h₀, C.h₁]; exact stdSimplex.ext _ _ fun i ↦ by fin_cases i; rfl)
    -- Its end over `1` lies over `b` and extends `a`.
    exact ⟨⟨⟨ι₁ ≫ L, by rw [← ι₁_comp_assoc, hL, sq₁.fac_left],
      by rw [Category.assoc, hLp, C.h₁_assoc, Category.id_comp]⟩⟩⟩

end RightFibration

namespace LeftFibration

/-- **A left fibration over a Kan complex is a Kan fibration**, dually to HTT Lemma 2.1.3.3: its
opposite is a right fibration over the Kan complex `Yᵒᵖ`. -/
theorem fibration_of_kanComplex (p : X ⟶ Y) [LeftFibration p] [KanComplex Y] :
    Fibration p :=
  (fibration_opFunctor_map_iff p).1 (RightFibration.fibration_of_kanComplex (opFunctor.map p))

end LeftFibration

/-- The fibres of a left fibration are Kan complexes. -/
instance fiber.kanComplex_of_leftFibration (q : X ⟶ Y) [LeftFibration q] (y : Y _⦋0⦌) :
    KanComplex (fiber q y) := by
  have := kanComplex_of_isTerminal (Subcomplex.isTerminalOfSimplex y)
  have := LeftFibration.fibration_of_kanComplex ((Subcomplex.ofSimplex y).fromPreimage q)
  -- `fiber q y` is the source of the restriction of `q` over `ofSimplex y`.
  rw [fiber_eq_preimage]
  exact isFibrant_of_fibration ((Subcomplex.ofSimplex y).fromPreimage q)

namespace LeftFibration

/-- **A left fibration is a trivial fibration exactly when its fibres are weakly contractible**,
dually to HTT Lemma 2.1.3.4. Its opposite is a right fibration, whose fibres are the opposites of
the fibres of `p` (`SSet.fiber_opFunctor_map`), and a Kan complex is weakly contractible exactly
when its opposite is (`SSet.isWeaklyContractible_op_iff`). -/
theorem rlp_monomorphisms_iff_isWeaklyContractible_fiber (p : X ⟶ Y) [LeftFibration p] :
    (monomorphisms SSet.{u}).rlp p ↔ ∀ y : Y _⦋0⦌, IsWeaklyContractible (fiber p y : SSet.{u}) := by
  rw [← rlp_monomorphisms_opFunctor_map_iff,
    RightFibration.rlp_monomorphisms_iff_isWeaklyContractible_fiber]
  refine opObjEquiv.forall_congr fun y ↦ ?_
  have h := fiber_opFunctor_map p (opObjEquiv y)
  rw [Equiv.symm_apply_apply] at h
  rw [h, ← isWeaklyContractible_op_iff (fiber p (opObjEquiv y) : SSet.{u})]
  exact ⟨fun _ ↦ .of_iso (Subcomplex.opIso _).symm, fun _ ↦ .of_iso (Subcomplex.opIso _)⟩

end LeftFibration

end SSet
