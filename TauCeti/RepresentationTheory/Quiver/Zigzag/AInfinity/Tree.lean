/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.Preprojective.Signless.Affine.Tree
public import TauCeti.RepresentationTheory.Quiver.Zigzag.AInfinity.Affine.D.Basic
public import TauCeti.RepresentationTheory.Quiver.Zigzag.AInfinity.Affine.E

/-!
# Higher Hochschild classes and non-formality of non-Dynkin trees

Every finite tree which is not isomorphic to a Dynkin diagram contains a copy of an affine diagram
`Dₙ` (`n ≥ 4`), `E₆`, `E₇` or `E₈`
(`SimpleGraph.IsTree.isContained_affineDynkinType_of_not_exists_dynkinType_iso`). Combining the
corresponding matrix-trace detections gives both a nonzero Hochschild class `HH^{n, 2 - n}` in
arity `n ∈ {4, 6, 8, 12}` over every nontrivial commutative ring, and — both over every nontrivial
`ℚ`-algebra and over every commutative ring `k` in which `(2 : k)` is not a unit (in particular in
characteristic `2` and over `ℤ`) — a non-formal minimal strictly unital single-walk loop
deformation in that arity. Hence neither the strict zigzag algebra on the relation quotient nor the
public path-graded zigzag algebra `TauCeti.zigzagAlgebra k G` of a finite non-Dynkin tree is
intrinsically formal (`SimpleGraph.IsTree.not_isZigzagAlgebraIntrinsicallyFormal` and
`SimpleGraph.IsTree.not_isZigzagAlgebraIntrinsicallyFormal_of_not_isUnit_two`, the non-Dynkin
implication of Liu and Wang's Theorem 1.1).

## Main results

* `SimpleGraph.IsTree.exists_not_hochschildVanishesAt_zigzagStrictAInfinityAlgebra`: over every
  nontrivial commutative ring, a finite non-Dynkin tree has `HH^{n, 2 - n} ≠ 0` for some
  `n ∈ {4, 6, 8, 12}`.
* `SimpleGraph.IsTree.exists_not_isFormal_zigzagLoopAInfinityAlgebra`,
  `SimpleGraph.IsTree.not_isIntrinsicallyFormal_zigzagStrictAInfinityAlgebra` (and their
  `_of_not_isUnit_two` companions): over every nontrivial `ℚ`-algebra or when `(2 : k)` is not a
  unit, some single-walk loop deformation in arity `4`, `6`, `8` or `12` is not formal and the
  strict zigzag algebra is not intrinsically formal.
* `SimpleGraph.IsTree.exists_isZigzagAInfinityDeformation_not_isFormal` and
  `SimpleGraph.IsTree.not_isZigzagAlgebraIntrinsicallyFormal` (and their `_of_not_isUnit_two`
  companions): over every nontrivial `ℚ`-algebra or when `(2 : k)` is not a unit, every finite
  non-Dynkin tree admits a non-formal `IsZigzagAInfinityDeformation` and fails
  `IsZigzagAlgebraIntrinsicallyFormal`.

## References

* Junyang Liu and Zhengfang Wang, *A-infinity deformations of zigzag algebras via Ginzburg dg
  algebras*,
  https://arxiv.org/abs/2301.06757, Theorem 1.1 and Sections 3--4.
* T. Kadeishvili, *The structure of the `A(∞)`-algebra, and the Hochschild and Harrison
  cohomologies*, Trudy Tbiliss. Mat. Inst. 91 (1988), 19--27.
-/

public section

namespace SimpleGraph.IsTree

open TauCeti

variable {k : Type*} [CommRing k] {V : Type*} [Finite V] {G : SimpleGraph V}
  {hns : ∀ i : V, ∃ j, G.Adj i j}

/-- **The zigzag algebra of a non-Dynkin tree has a nonzero higher Hochschild class.** If a finite
tree `G` is not isomorphic to the diagram of any valid Dynkin type, then over every nontrivial
commutative ring the Hochschild cohomology `HH^{n, 2 - n}` of the strict zigzag algebra of `G` is
nonzero for some `n ∈ {4, 6, 8, 12}`: some loop operation of a closed walk of length `n` is a
Hochschild cocycle which is not a coboundary. In particular Kadeishvili's criterion
`TauCeti.AInfinityAlgebra.isIntrinsicallyFormal_of_forall_hochschildVanishesAt` does not apply. -/
theorem exists_not_hochschildVanishesAt_zigzagStrictAInfinityAlgebra [Nontrivial k] (hG : G.IsTree)
    (hD : ¬ ∃ t : DynkinType, t.Valid ∧ Nonempty (G ≃g diagramGraph t.cartanMatrix)) :
    ∃ n : {n : ℕ // 1 < n}, (n : ℕ) ∈ ({4, 6, 8, 12} : Finset ℕ) ∧
      ¬(zigzagStrictAInfinityAlgebra k hns).HochschildVanishesAt n := by
  classical
  have := Fintype.ofFinite V
  rcases hG.isContained_affineDynkinType_of_not_exists_dynkinType_iso hD with
    ⟨n, hn, h⟩ | h | h | h
  · exact ⟨⟨4, by norm_num⟩, by simp,
      not_hochschildVanishesAt_four_zigzagStrictAInfinityAlgebra_of_isContained hn h⟩
  · exact ⟨⟨6, by norm_num⟩, by simp,
      not_hochschildVanishesAt_six_zigzagStrictAInfinityAlgebra h⟩
  · exact ⟨⟨8, by norm_num⟩, by simp,
      not_hochschildVanishesAt_eight_zigzagStrictAInfinityAlgebra h⟩
  · exact ⟨⟨12, by norm_num⟩, by simp,
      not_hochschildVanishesAt_twelve_zigzagStrictAInfinityAlgebra h⟩

/-- Common `Dₙ / E₆ / E₇ / E₈` case split for single-walk non-formality on non-Dynkin trees,
parameterized by single-walk non-formality along copies of affine `E₆`, `E₇` and `E₈`. -/
private theorem exists_not_isFormal_zigzagLoopAInfinityAlgebra_of_affineE [Nontrivial k]
    (hG : G.IsTree)
    (hD : ¬ ∃ t : DynkinType, t.Valid ∧ Nonempty (G ≃g diagramGraph t.cartanMatrix))
    (hE6 : ∀ f : AffineDynkinType.E6.graph.Copy G,
      ¬(zigzagLoopAInfinityAlgebra hns
        (Finsupp.single (fun t ↦ f.toHom.mapDart (affineE6Walk t)) (1 : k))
        (fst_eq_snd_of_mem_support_single
          (fun i ↦ congrArg f (affineE6Walk_fst_eq_snd i)) 1)).IsFormal)
    (hE7 : ∀ f : AffineDynkinType.E7.graph.Copy G,
      ¬(zigzagLoopAInfinityAlgebra hns
        (Finsupp.single (fun t ↦ f.toHom.mapDart (affineE7Walk t)) (1 : k))
        (fst_eq_snd_of_mem_support_single
          (fun i ↦ congrArg f (affineE7Walk_fst_eq_snd i)) 1)).IsFormal)
    (hE8 : ∀ f : AffineDynkinType.E8.graph.Copy G,
      ¬(zigzagLoopAInfinityAlgebra hns
        (Finsupp.single (fun t ↦ f.toHom.mapDart (affineE8Walk t)) (1 : k))
        (fst_eq_snd_of_mem_support_single
          (fun i ↦ congrArg f (affineE8Walk_fst_eq_snd i)) 1)).IsFormal) :
    ∃ (n : ℕ) (_ : NeZero n), n ∈ ({4, 6, 8, 12} : Finset ℕ) ∧
      ∃ (w : Fin n → G.Dart) (hw : ∀ i, (w i).fst = (w (i + 1)).snd),
        ¬(zigzagLoopAInfinityAlgebra hns (Finsupp.single w (1 : k))
          (fst_eq_snd_of_mem_support_single hw 1)).IsFormal := by
  classical
  have := Fintype.ofFinite V
  rcases hG.isContained_affineDynkinType_of_not_exists_dynkinType_iso hD with
    ⟨m, hm, ⟨f⟩⟩ | hE6' | hE7' | hE8'
  · exact ⟨4, inferInstance, by simp, fun t ↦ f.toHom.mapDart (affineDWalk hm t),
      fun i ↦ congrArg f (affineDWalk_fst_eq_snd hm i),
      not_isFormal_zigzagLoopAInfinityAlgebra_affineDWalk hm f⟩
  · obtain ⟨f⟩ := hE6'
    exact ⟨6, inferInstance, by simp, fun t ↦ f.toHom.mapDart (affineE6Walk t),
      fun i ↦ congrArg f (affineE6Walk_fst_eq_snd i), hE6 f⟩
  · obtain ⟨f⟩ := hE7'
    exact ⟨8, inferInstance, by simp, fun t ↦ f.toHom.mapDart (affineE7Walk t),
      fun i ↦ congrArg f (affineE7Walk_fst_eq_snd i), hE7 f⟩
  · obtain ⟨f⟩ := hE8'
    exact ⟨12, inferInstance, by simp, fun t ↦ f.toHom.mapDart (affineE8Walk t),
      fun i ↦ congrArg f (affineE8Walk_fst_eq_snd i), hE8 f⟩

/-- **A non-Dynkin tree admits a non-formal single-walk loop deformation in arity `4`, `6`, `8` or
`12`** over every nontrivial `ℚ`-algebra: if a finite tree `G` is not isomorphic to the diagram of
any valid Dynkin type, then for some `n ∈ {4, 6, 8, 12}` there is a closed walk of length `n` whose
single-walk loop deformation of the strict zigzag algebra of `G` is not formal. -/
theorem exists_not_isFormal_zigzagLoopAInfinityAlgebra [Nontrivial k] [Algebra ℚ k] (hG : G.IsTree)
    (hD : ¬ ∃ t : DynkinType, t.Valid ∧ Nonempty (G ≃g diagramGraph t.cartanMatrix)) :
    ∃ (n : ℕ) (_ : NeZero n), n ∈ ({4, 6, 8, 12} : Finset ℕ) ∧
      ∃ (w : Fin n → G.Dart) (hw : ∀ i, (w i).fst = (w (i + 1)).snd),
        ¬(zigzagLoopAInfinityAlgebra hns (Finsupp.single w (1 : k))
          (fst_eq_snd_of_mem_support_single hw 1)).IsFormal :=
  exists_not_isFormal_zigzagLoopAInfinityAlgebra_of_affineE hG hD
    not_isFormal_zigzagLoopAInfinityAlgebra_affineE6Walk
    not_isFormal_zigzagLoopAInfinityAlgebra_affineE7Walk
    not_isFormal_zigzagLoopAInfinityAlgebra_affineE8Walk

/-- **A non-Dynkin tree admits a non-formal single-walk loop deformation in arity `4`, `6`, `8` or
`12`** over every commutative ring in which `(2 : k)` is not a unit (in particular in
characteristic `2` and over `ℤ`). -/
theorem exists_not_isFormal_zigzagLoopAInfinityAlgebra_of_not_isUnit_two (h2 : ¬IsUnit (2 : k))
    (hG : G.IsTree)
    (hD : ¬ ∃ t : DynkinType, t.Valid ∧ Nonempty (G ≃g diagramGraph t.cartanMatrix)) :
    ∃ (n : ℕ) (_ : NeZero n), n ∈ ({4, 6, 8, 12} : Finset ℕ) ∧
      ∃ (w : Fin n → G.Dart) (hw : ∀ i, (w i).fst = (w (i + 1)).snd),
        ¬(zigzagLoopAInfinityAlgebra hns (Finsupp.single w (1 : k))
          (fst_eq_snd_of_mem_support_single hw 1)).IsFormal :=
  have : Nontrivial k := ⟨⟨2, 1, fun h ↦ h2 (h ▸ isUnit_one)⟩⟩
  exists_not_isFormal_zigzagLoopAInfinityAlgebra_of_affineE hG hD
    (not_isFormal_zigzagLoopAInfinityAlgebra_affineE6Walk_of_not_isUnit_two h2)
    (not_isFormal_zigzagLoopAInfinityAlgebra_affineE7Walk_of_not_isUnit_two h2)
    (not_isFormal_zigzagLoopAInfinityAlgebra_affineE8Walk_of_not_isUnit_two h2)

/-- **The strict zigzag algebra of a non-Dynkin tree is not intrinsically formal** over every
nontrivial `ℚ`-algebra (in particular over every field of characteristic zero). -/
theorem not_isIntrinsicallyFormal_zigzagStrictAInfinityAlgebra [Nontrivial k] [Algebra ℚ k]
    (hG : G.IsTree)
    (hD : ¬ ∃ t : DynkinType, t.Valid ∧ Nonempty (G ≃g diagramGraph t.cartanMatrix)) :
    ¬(zigzagStrictAInfinityAlgebra k hns).IsIntrinsicallyFormal := by
  obtain ⟨_, _, _, _, _, hnf⟩ :=
    hG.exists_not_isFormal_zigzagLoopAInfinityAlgebra (k := k) (hns := hns) hD
  exact not_isIntrinsicallyFormal_zigzagStrictAInfinityAlgebra_of_not_isFormal hnf

/-- **The strict zigzag algebra of a non-Dynkin tree is not intrinsically formal** whenever
`(2 : k)` is not a unit (for instance in characteristic `2` or over `ℤ`). -/
theorem not_isIntrinsicallyFormal_zigzagStrictAInfinityAlgebra_of_not_isUnit_two
    (h2 : ¬IsUnit (2 : k)) (hG : G.IsTree)
    (hD : ¬ ∃ t : DynkinType, t.Valid ∧ Nonempty (G ≃g diagramGraph t.cartanMatrix)) :
    ¬(zigzagStrictAInfinityAlgebra k hns).IsIntrinsicallyFormal := by
  obtain ⟨_, _, _, _, _, hnf⟩ :=
    hG.exists_not_isFormal_zigzagLoopAInfinityAlgebra_of_not_isUnit_two (hns := hns) h2 hD
  exact not_isIntrinsicallyFormal_zigzagStrictAInfinityAlgebra_of_not_isFormal hnf

/-- Transport a non-formal loop deformation of the strict zigzag algebra on a non-Dynkin tree to
a non-formal `IsZigzagAInfinityDeformation` of the public zigzag algebra `zigzagAlgebra k G`. -/
private theorem exists_isZigzagAInfinityDeformation_not_isFormal_of_exists_loop
    (hG : G.IsTree)
    (hD : ¬ ∃ t : DynkinType, t.Valid ∧ Nonempty (G ≃g diagramGraph t.cartanMatrix))
    (hw : ∀ hns : ∀ i : V, ∃ j, G.Adj i j,
      ∃ (n : ℕ) (_ : NeZero n) (c : (Fin n → G.Dart) →₀ k)
        (hc : ∀ w ∈ c.support, ∀ i, (w i).fst = (w (i + 1)).snd),
        ¬(zigzagLoopAInfinityAlgebra hns c hc).IsFormal) :
    ∃ 𝒜 : AInfinityAlgebra k (zigzagAlgebra k G),
      IsZigzagAInfinityDeformation k G 𝒜 ∧ ¬𝒜.IsFormal := by
  obtain ⟨t, ht, -, h⟩ :=
    hG.connected.exists_isContained_affineDynkinType_of_not_exists_dynkinType_iso hD
  have : Nontrivial V := t.nontrivial_of_graph_isContained ht h
  obtain ⟨_, _, c, hc, hnf⟩ := hw hG.connected.preconnected.exists_adj_of_nontrivial
  exact ⟨zigzagAlgebraLoopAInfinityAlgebra hG.connected c hc,
    isZigzagAInfinityDeformation_zigzagAlgebraLoopAInfinityAlgebra hG.connected c hc,
    (isFormal_zigzagAlgebraLoopAInfinityAlgebra_iff hG.connected c hc).not.mpr hnf⟩

/-- **Every finite non-Dynkin tree admits a non-formal minimal strictly unital `A∞` deformation** of
its public zigzag algebra `zigzagAlgebra k G`, over any nontrivial `ℚ`-algebra (in particular over
any field of characteristic zero). -/
theorem exists_isZigzagAInfinityDeformation_not_isFormal [Nontrivial k] [Algebra ℚ k]
    (hG : G.IsTree)
    (hD : ¬ ∃ t : DynkinType, t.Valid ∧ Nonempty (G ≃g diagramGraph t.cartanMatrix)) :
    ∃ 𝒜 : AInfinityAlgebra k (zigzagAlgebra k G),
      IsZigzagAInfinityDeformation k G 𝒜 ∧ ¬𝒜.IsFormal :=
  exists_isZigzagAInfinityDeformation_not_isFormal_of_exists_loop hG hD fun hns ↦
    let ⟨n, hn, _, w, hw, hnf⟩ :=
      hG.exists_not_isFormal_zigzagLoopAInfinityAlgebra (k := k) (hns := hns) hD
    ⟨n, hn, Finsupp.single w (1 : k), fst_eq_snd_of_mem_support_single hw 1, hnf⟩

/-- **Every finite non-Dynkin tree admits a non-formal minimal strictly unital `A∞` deformation** of
its public zigzag algebra `zigzagAlgebra k G` whenever `(2 : k)` is not a unit (for instance in
characteristic `2` or over `ℤ`). -/
theorem exists_isZigzagAInfinityDeformation_not_isFormal_of_not_isUnit_two (h2 : ¬IsUnit (2 : k))
    (hG : G.IsTree)
    (hD : ¬ ∃ t : DynkinType, t.Valid ∧ Nonempty (G ≃g diagramGraph t.cartanMatrix)) :
    ∃ 𝒜 : AInfinityAlgebra k (zigzagAlgebra k G),
      IsZigzagAInfinityDeformation k G 𝒜 ∧ ¬𝒜.IsFormal :=
  exists_isZigzagAInfinityDeformation_not_isFormal_of_exists_loop hG hD fun hns ↦
    let ⟨n, hn, _, w, hw, hnf⟩ :=
      hG.exists_not_isFormal_zigzagLoopAInfinityAlgebra_of_not_isUnit_two (hns := hns) h2 hD
    ⟨n, hn, Finsupp.single w (1 : k), fst_eq_snd_of_mem_support_single hw 1, hnf⟩

/-- **The public zigzag algebra of a finite non-Dynkin tree is not intrinsically formal**, over any
nontrivial `ℚ`-algebra (in particular over any field of characteristic zero). This proves the
non-Dynkin implication of Liu and Wang's Theorem 1.1 on `TauCeti.zigzagAlgebra k G`. -/
theorem not_isZigzagAlgebraIntrinsicallyFormal [Nontrivial k] [Algebra ℚ k] (hG : G.IsTree)
    (hD : ¬ ∃ t : DynkinType, t.Valid ∧ Nonempty (G ≃g diagramGraph t.cartanMatrix)) :
    ¬IsZigzagAlgebraIntrinsicallyFormal k G := by
  obtain ⟨𝒜, h𝒜, hnf⟩ := hG.exists_isZigzagAInfinityDeformation_not_isFormal (k := k) hD
  exact fun hf ↦ hnf (hf.isFormal h𝒜)

/-- **The public zigzag algebra of a finite non-Dynkin tree is not intrinsically formal** whenever
`(2 : k)` is not a unit (for instance in characteristic `2` or over `ℤ`). -/
theorem not_isZigzagAlgebraIntrinsicallyFormal_of_not_isUnit_two (h2 : ¬IsUnit (2 : k))
    (hG : G.IsTree)
    (hD : ¬ ∃ t : DynkinType, t.Valid ∧ Nonempty (G ≃g diagramGraph t.cartanMatrix)) :
    ¬IsZigzagAlgebraIntrinsicallyFormal k G := by
  obtain ⟨𝒜, h𝒜, hnf⟩ :=
    hG.exists_isZigzagAInfinityDeformation_not_isFormal_of_not_isUnit_two (k := k) h2 hD
  exact fun hf ↦ hnf (hf.isFormal h𝒜)

end SimpleGraph.IsTree
