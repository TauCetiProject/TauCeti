/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Pinning.Isomorphism
public import TauCeti.Algebra.AlgebraicGroup.Tangent.RootSpace.BaseChange
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Tangent.BaseChange

/-!
# Base change of pinnings

Let `P` be a pinning (`TauCeti.Pinning`) of a smooth affine group `G = Spec H` over a ring `R`
with connected spectrum, and let `R → S` be an injective map to a ring with connected spectrum.
This file constructs the base-changed pinning `P.baseChange S` of `G_S = Spec (S ⊗[R] H)`:

* its split maximal torus is the base change of the torus of `P`
  (`TauCeti.SplitMaximalTorus.baseChange`);
* its Borel subgroup is the base change of the Borel subgroup of `P`
  (`TauCeti.CommHopfAlgCat.baseChangeHopfIdeal`, a Borel by
  `TauCeti.HopfIdeal.IsBorelOver.baseChange`);
* its simple roots are those of `P`, and its root vector at a simple root `α` is the scalar
  extension `1 ⊗ X_α` of the root vector `X_α` of `P`, read in the Lie algebra of `G_S` through
  `Derivation.cotangentDualBaseChangeEquiv`.

The substance is that base change does not change the simple roots. The simple roots are not
part of the data of a pinning but are read off from the torus and the Borel subgroup: they are
the positive roots, the nontrivial adjoint weights whose root space lies in the Lie algebra of the
Borel subgroup, which are not sums of two positive roots. Each root space is a direct summand of
the Lie algebra, which is projective, so along an injective map `R → S` it vanishes after base
change only if it vanishes (`Derivation.nontrivialAdjointWeights_baseChange`); and a tangent
vector `x` lies in the Lie algebra of the Borel subgroup exactly when `1 ⊗ x` lies in the Lie
algebra of its base change (`TauCeti.CommHopfAlgCat` lemma
`cotangentDualBaseChangeEquiv_one_tmul_mem_lieSubalgebra_baseChangeHopfIdeal_iff`).
Injectivity of `R → S`, as the class `FaithfulSMul R S`, holds for every faithfully flat map
(`Module.FaithfullyFlat.faithfulSMul`), in particular every field extension, and for the map from
`ℤ` to a ring of characteristic zero, which is how a pinning of a Chevalley group over `ℤ` gives a
pinning over a field of characteristic zero.

Base change of pinnings is compatible with the identity, with composites of ring maps and with
transport along isomorphisms of coordinate algebras (`TauCeti.Pinning.comapOfIso`). Pinnings with
the same torus and Borel subgroup are equal once their root vectors agree
(`TauCeti.Pinning.ext_rootVector`), so these laws reduce to statements about tori, Borel
subgroups and root vectors.

For two independently given pinnings, `TauCeti.Pinning.rootSpaceBaseChangeEquiv` compares the
scalar extension of a simple root space of the first with a simple root space of the second
through the chosen generators. For a pinning and its base change this comparison is the
geometric comparison of root spaces `Derivation.adjointWeightSpaceBaseChangeEquiv`
(`TauCeti.Pinning.coe_rootSpaceBaseChangeEquiv_baseChange_apply`). For the standard pinnings of
`GL_{r+1}`, `SL_{r+1}` and `Sp_{2m}`, the base change is the standard pinning over the new ring
(`GeneralLinear.comapOfIso_baseChange_standardPinning` and its special-linear and symplectic
counterparts), each checked through `TauCeti.Pinning.comapOfIso_baseChange_eq`, which recognizes
a base change transported along an isomorphism from its torus, Borel subgroup and root vectors.

## Main declarations

* `TauCeti.SplitMaximalTorus.isPositiveRoot_baseChange_iff` and
  `TauCeti.SplitMaximalTorus.isSimpleRoot_baseChange_iff`: positive and simple roots are invariant
  under base change along an injective map.
* `TauCeti.Pinning.baseChange`: the base change of a pinning, with simple roots those of the
  original pinning (`TauCeti.Pinning.isSimpleRoot_baseChange_iff`).
* `TauCeti.Pinning.baseChange_rootVector`: its root vectors are the scalar extensions `1 ⊗ X_α`.
* `TauCeti.Pinning.comapOfIso_baseChange_self`, `TauCeti.Pinning.baseChange_baseChange` and
  `TauCeti.Pinning.baseChange_comapOfIso`: the laws for the identity, for composites and for
  transport along isomorphisms.
* `TauCeti.Pinning.comapOfIso_baseChange_eq`: recognizing a transported base change of a pinning.

## References

* B. Conrad, *Reductive Group Schemes* (2014), Definition 6.1.1 and Remark 6.1.2.
* J. S. Milne, *Algebraic Groups* (2017), §21.1 (positive and simple roots).
-/

public section

open CategoryTheory
open scoped TensorProduct

namespace TauCeti

universe u v

section RootSpaceComparison

namespace Pinning

noncomputable section

variable {R : Type u} {K : Type v} [CommRing R] [CommRing K] [Algebra R K]
  {H : CommHopfAlgCat.{u} R} {H' : CommHopfAlgCat.{v} K}
  [Algebra.FiniteType R H] [Algebra.FiniteType K H']
  [Algebra.Smooth R H] [Algebra.Smooth K H']
  [ConnectedSpace (PrimeSpectrum R)] [ConnectedSpace (PrimeSpectrum K)]
  {r s : ℕ} (P : Pinning R H r) (Q : Pinning K H' s)
  (α : {α // P.torus.IsSimpleRoot P.borel α})
  (β : {β // Q.torus.IsSimpleRoot Q.borel β})

/-- Identify a scalar-extended simple root space with another pinned simple root
space using their chosen trivializations. -/
def rootSpaceBaseChangeEquiv :
    K ⊗[R] Derivation.adjointWeightSpace P.torus.coordinateMap.hom
        (Multiplicative.ofAdd α.val) ≃ₗ[K]
      Derivation.adjointWeightSpace Q.torus.coordinateMap.hom
        (Multiplicative.ofAdd β.val) :=
  ((P.rootSpaceEquiv α).symm.baseChange R K _ _).trans
    ((TensorProduct.AlgebraTensorModule.rid R K K).trans (Q.rootSpaceEquiv β))

/-- The root-space comparison preserves the chosen scalar coordinates. -/
@[simp↓]
theorem rootSpaceBaseChangeEquiv_tmul (c : K) (b : R) :
    P.rootSpaceBaseChangeEquiv Q α β (c ⊗ₜ[R] P.rootSpaceEquiv α b) =
      Q.rootSpaceEquiv β (c * algebraMap R K b) := by
  simp only [rootSpaceBaseChangeEquiv, LinearEquiv.trans_apply,
    LinearEquiv.baseChange_tmul, LinearEquiv.symm_apply_apply,
    TensorProduct.AlgebraTensorModule.rid_tmul, Algebra.smul_def]
  rw [mul_comm]

/-- The inverse comparison expresses a chosen vector as its scalar coordinate
times the chosen generator over the original base. -/
@[simp↓]
theorem rootSpaceBaseChangeEquiv_symm_apply (c : K) :
    (P.rootSpaceBaseChangeEquiv Q α β).symm (Q.rootSpaceEquiv β c) =
      c ⊗ₜ[R] P.rootSpaceEquiv α 1 := by
  apply (P.rootSpaceBaseChangeEquiv Q α β).symm_apply_eq.mpr
  rw [rootSpaceBaseChangeEquiv_tmul, map_one, mul_one]

end

end Pinning

end RootSpaceComparison

variable {R : Type u} [CommRing R] {H : CommHopfAlgCat.{u} R} [Algebra.FiniteType R H] {r : ℕ}

namespace SplitMaximalTorus

variable (S : Type u) [CommRing S] [Algebra R S] [FaithfulSMul R S]
  [Module.Finite R (Bialgebra.CotangentSpace R H)]
  [Module.Projective R (Bialgebra.CotangentSpace R H)]
  [Module.Finite S (Bialgebra.CotangentSpace S (S ⊗[R] H))]
  [Module.Projective S (Bialgebra.CotangentSpace S (S ⊗[R] H))]

open _root_.TauCeti.CommHopfAlgCat in
/-- **Positive roots are invariant under base change along an injective map** `R → S`: a
character is a positive root for the base-changed torus and the base-changed subgroup exactly
when it is one for the original torus and subgroup. -/
@[simp]
theorem isPositiveRoot_baseChange_iff (T : SplitMaximalTorus R H r) (B : HopfIdeal R H)
    (α : ULift.{u} (Fin r) →₀ ℤ) :
    (T.baseChange S).IsPositiveRoot (CommHopfAlgCat.baseChangeHopfIdeal (K := S) B) α ↔
      T.IsPositiveRoot B α := by
  rw [isPositiveRoot_iff, isPositiveRoot_iff, nontrivialAdjointWeights_baseChange]
  refine and_congr_right fun _ ↦ ?_
  rw [adjointWeightSpace_baseChange S T (Multiplicative.ofAdd α)]
  constructor
  · intro h x hx
    exact (cotangentDualBaseChangeEquiv_one_tmul_mem_lieSubalgebra_baseChangeHopfIdeal_iff B x).mp
      (h _ (Submodule.mem_map_of_mem (Submodule.tmul_mem_baseChange_of_mem 1 hx)))
  · intro h y hy
    obtain ⟨z, hz, rfl⟩ := Submodule.mem_map.mp hy
    clear hy
    rw [Submodule.baseChange_eq_span] at hz
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨x, hx, rfl⟩ := hz
      exact cotangentDualBaseChangeEquiv_tmul_mem_lieSubalgebra_baseChangeHopfIdeal (h x hx) 1
    | zero => simpa only [map_zero] using zero_mem _
    | add z w _ _ hz hw => simpa only [map_add] using add_mem hz hw
    | smul c z _ hz =>
      rw [map_smul, LinearEquiv.map_smul]
      exact SMulMemClass.smul_mem c hz

/-- **Simple roots are invariant under base change along an injective map** `R → S`. -/
@[simp]
theorem isSimpleRoot_baseChange_iff (T : SplitMaximalTorus R H r) (B : HopfIdeal R H)
    (α : ULift.{u} (Fin r) →₀ ℤ) :
    (T.baseChange S).IsSimpleRoot (CommHopfAlgCat.baseChangeHopfIdeal (K := S) B) α ↔
      T.IsSimpleRoot B α := by
  simp only [isSimpleRoot_iff, isPositiveRoot_baseChange_iff]

end SplitMaximalTorus

namespace Pinning

variable [Algebra.Smooth R H] [ConnectedSpace (PrimeSpectrum R)]

variable (S : Type u) [CommRing S] [Algebra R S] [FaithfulSMul R S]
  [ConnectedSpace (PrimeSpectrum S)]

/-- **Base change of a pinning** along an injective map `R → S` to a ring with connected
spectrum. The torus and the Borel subgroup are base-changed, and the trivialization of each simple
root space is the scalar extension of the original one, read in the Lie algebra of the
base-changed group. The simple roots are those of the original pinning
(`TauCeti.Pinning.isSimpleRoot_baseChange_iff`). -/
noncomputable def baseChange (P : Pinning R H r) :
    Pinning S (CommHopfAlgCat.baseChange (K := S) H) r where
  reductive := P.reductive.baseChange S
  torus := P.torus.baseChange S
  borel := CommHopfAlgCat.baseChangeHopfIdeal (K := S) P.borel
  isBorel := P.isBorel.baseChange S
  borel_le_torus := by
    rw [SplitMaximalTorus.definingIdeal_baseChange]
    exact CommHopfAlgCat.baseChangeHopfIdeal_mono P.borel_le_torus
  rootSpaceEquiv α :=
    ((TensorProduct.AlgebraTensorModule.rid R S S).symm.trans
      ((P.rootSpaceEquiv ⟨α.val,
        (SplitMaximalTorus.isSimpleRoot_baseChange_iff S _ _ _).mp α.property⟩).baseChange
          R S _ _)).trans
      (Derivation.adjointWeightSpaceBaseChangeEquiv _ _
        (SplitMaximalTorus.baseChange_coordinateMap_hom_one_tmul S P.torus) _)

/-- The torus of a base-changed pinning is the base change of its torus. -/
@[simp]
theorem baseChange_torus (P : Pinning R H r) :
    (P.baseChange S).torus = P.torus.baseChange S :=
  (rfl)

/-- The Borel subgroup of a base-changed pinning is the base change of its Borel subgroup. -/
@[simp]
theorem baseChange_borel (P : Pinning R H r) :
    (P.baseChange S).borel = CommHopfAlgCat.baseChangeHopfIdeal (K := S) P.borel :=
  (rfl)

/-- The simple roots of a base-changed pinning are those of the original pinning. -/
theorem isSimpleRoot_baseChange_iff (P : Pinning R H r) (α : ULift.{u} (Fin r) →₀ ℤ) :
    (P.baseChange S).torus.IsSimpleRoot (P.baseChange S).borel α ↔
      P.torus.IsSimpleRoot P.borel α := by
  rw [baseChange_torus, baseChange_borel, SplitMaximalTorus.isSimpleRoot_baseChange_iff]

/-- The trivializations of a base-changed pinning send `c` to the scalar extension `c ⊗ X_α` of
the root vector of the original pinning at the same simple root. -/
@[simp]
theorem coe_baseChange_rootSpaceEquiv_apply (P : Pinning R H r)
    (α : {α // (P.baseChange S).torus.IsSimpleRoot (P.baseChange S).borel α}) (c : S) :
    ((P.baseChange S).rootSpaceEquiv α c :
        Module.Dual S (Bialgebra.CotangentSpace S (S ⊗[R] H))) =
      Derivation.cotangentDualBaseChangeEquiv R S H
        (c ⊗ₜ P.rootVector ⟨α.val, (P.isSimpleRoot_baseChange_iff S _).mp α.property⟩) := by
  -- The field is the composite of `rid.symm`, the scalar extension of the trivialization of `P`
  -- and the comparison of root spaces. Its codomain is stated for `(P.baseChange S).torus`, which
  -- is not syntactically `P.torus.baseChange S`, so `LinearEquiv.trans_apply` does not rewrite it:
  -- `exact` unfolds the composite, and `rfl` identifies `rid.symm c` with `c ⊗ 1`.
  exact (Derivation.coe_adjointWeightSpaceBaseChangeEquiv_tmul _ _ _ _ _ _).trans
    (by rw [rootVector_def]; rfl)

/-- **The root vectors of a base-changed pinning** are the scalar extensions `1 ⊗ X_α` of the root
vectors of the original pinning, at the same simple roots. -/
theorem baseChange_rootVector (P : Pinning R H r)
    (α : {α // (P.baseChange S).torus.IsSimpleRoot (P.baseChange S).borel α}) :
    (P.baseChange S).rootVector α =
      Derivation.cotangentDualBaseChangeEquiv R S H
        (1 ⊗ₜ P.rootVector ⟨α.val, (P.isSimpleRoot_baseChange_iff S _).mp α.property⟩) := by
  rw [rootVector_def, coe_baseChange_rootSpaceEquiv_apply]

/-- **Base change of a pinning identifies root spaces geometrically**: the comparison
`TauCeti.Pinning.rootSpaceBaseChangeEquiv` of a simple root space of `P`, extended to `S`, with the
simple root space of `P.baseChange S` at the same root is the comparison of root spaces induced by
the comparison of Lie algebras, `Derivation.adjointWeightSpaceBaseChangeEquiv`. -/
theorem coe_rootSpaceBaseChangeEquiv_baseChange_apply (P : Pinning R H r)
    (α : {α // P.torus.IsSimpleRoot P.borel α})
    (x : S ⊗[R] Derivation.adjointWeightSpace P.torus.coordinateMap.hom
      (Multiplicative.ofAdd α.val)) :
    (P.rootSpaceBaseChangeEquiv (P.baseChange S) α
        ⟨α.val, (P.isSimpleRoot_baseChange_iff S _).mpr α.property⟩ x :
        Module.Dual S (Bialgebra.CotangentSpace S (S ⊗[R] H))) =
      Derivation.adjointWeightSpaceBaseChangeEquiv _ _
        (SplitMaximalTorus.baseChange_coordinateMap_hom_one_tmul S P.torus)
        (Multiplicative.ofAdd α.val) x := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => rw [map_add, map_add, Submodule.coe_add, Submodule.coe_add, hx, hy]
  | tmul c x =>
    obtain ⟨b, rfl⟩ := (P.rootSpaceEquiv α).surjective x
    rw [rootSpaceBaseChangeEquiv_tmul, coe_baseChange_rootSpaceEquiv_apply]
    refine Eq.trans ?_ (Derivation.coe_adjointWeightSpaceBaseChangeEquiv_tmul _ _ _ _ c _).symm
    rw [rootVector_def]
    conv_rhs => rw [← mul_one b, ← smul_eq_mul, map_smul, Submodule.coe_smul,
      TensorProduct.tmul_smul, TensorProduct.smul_tmul']
    congr 2
    rw [Algebra.smul_def, mul_comm]

/-- **Base change of a pinning along the identity is trivial**: the base change of `P` along
`R → R`, transported along `H ≅ R ⊗[R] H`, is `P`. -/
@[simp]
theorem comapOfIso_baseChange_self (P : Pinning R H r) :
    (P.baseChange R).comapOfIso (CommHopfAlgCat.baseChangeSelfIso H).symm = P := by
  refine ext_rootVector ?_ ?_ fun α hP hQ ↦ ?_
  · rw [comapOfIso_torus, baseChange_torus, SplitMaximalTorus.comapOfIso_baseChange_self]
  · rw [comapOfIso_borel, baseChange_borel]
    exact CommHopfAlgCat.baseChangeHopfIdeal_comapOfSurjective_baseChangeSelfIso_inv P.borel
  · rw [comapOfIso_rootVector, baseChange_rootVector, Iso.symm_hom,
      CommHopfAlgCat.hom_baseChangeSelfIso_inv,
      Derivation.dualCotangentMap_lid_symm_cotangentDualBaseChangeEquiv, TensorProduct.lid_tmul,
      one_smul]

/-- **Base change of pinnings composes in stages**: for a tower `R → S → S'` of injective maps,
base-changing `P` to `S` and then to `S'` gives its base change to `S'`, transported along the
tower identification `S' ⊗[S] (S ⊗[R] H) ≅ S' ⊗[R] H`. -/
theorem baseChange_baseChange (S' : Type u) [CommRing S'] [Algebra R S'] [Algebra S S']
    [IsScalarTower R S S'] [FaithfulSMul S S'] [ConnectedSpace (PrimeSpectrum S')]
    (P : Pinning R H r) :
    haveI := FaithfulSMul.trans R S S'
    (P.baseChange S).baseChange S' =
      (P.baseChange S').comapOfIso (CommHopfAlgCat.baseChangeTowerIso R S' H) := by
  have := FaithfulSMul.trans R S S'
  refine ext_rootVector ?_ ?_ fun α hP hQ ↦ ?_
  · rw [comapOfIso_torus, baseChange_torus, baseChange_torus, baseChange_torus,
      SplitMaximalTorus.baseChange_baseChange]
  · rw [comapOfIso_borel, baseChange_borel, baseChange_borel, baseChange_borel]
    exact CommHopfAlgCat.baseChangeHopfIdeal_baseChangeHopfIdeal R S' P.borel
  · rw [comapOfIso_rootVector, baseChange_rootVector, baseChange_rootVector,
      baseChange_rootVector, CommHopfAlgCat.hom_baseChangeTowerIso_hom]
    exact (Derivation.dualCotangentMap_baseChangeTowerBialgEquiv_cotangentDualBaseChangeEquiv_tmul
      (T := S') 1 _).symm

/-- **Recognizing a transported base change of a pinning.** For an isomorphism
`e : S ⊗[R] H ≅ L` and a pinning `Q` of `L`, the base change of `P` transported along `e` is `Q`
once the transported torus and Borel subgroup are those of `Q` and the differential of `e⁻¹` sends
each extended root vector `1 ⊗ X_α` of `P` to the root vector of `Q` at the same simple root. -/
theorem comapOfIso_baseChange_eq {L : CommHopfAlgCat.{u} S} [Algebra.FiniteType S L]
    [Algebra.Smooth S L] (P : Pinning R H r) (Q : Pinning S L r)
    (e : CommHopfAlgCat.baseChange (K := S) H ≅ L)
    (htorus : (P.torus.baseChange S).comapOfIso e.symm = Q.torus)
    (hborel : (CommHopfAlgCat.baseChangeHopfIdeal (K := S) P.borel).map e.hom.hom = Q.borel)
    (hroot : ∀ (α : {α // P.torus.IsSimpleRoot P.borel α})
      (hQ : Q.torus.IsSimpleRoot Q.borel α.val),
      Derivation.dualCotangentMap e.inv.hom
          (Derivation.cotangentDualBaseChangeEquiv R S H (1 ⊗ₜ P.rootVector α)) =
        Q.rootVector ⟨α.val, hQ⟩) :
    (P.baseChange S).comapOfIso e.symm = Q := by
  refine ext_rootVector ?_ ?_ fun α _ hQ ↦ ?_
  · rw [comapOfIso_torus, baseChange_torus, htorus]
  · rw [comapOfIso_borel, baseChange_borel]
    exact (CommHopfAlgCat.comapOfSurjective_inv_eq_map_hom _ _).trans hborel
  · rw [comapOfIso_rootVector, baseChange_rootVector, Iso.symm_hom]
    exact hroot _ hQ

-- The map `ℤ → K` to a field of characteristic zero is injective (`FaithfulSMul ℤ K`), so a pinning
-- over `ℤ`, for instance of a Chevalley group, base-changes to every such field.
noncomputable example {H : CommHopfAlgCat.{0} ℤ} [Algebra.FiniteType ℤ H] [Algebra.Smooth ℤ H]
    (P : Pinning ℤ H r) (K : Type) [Field K] [CharZero K] :
    Pinning K (CommHopfAlgCat.baseChange (K := K) H) r :=
  P.baseChange K

variable {L : CommHopfAlgCat.{u} R} [Algebra.FiniteType R L] [Algebra.Smooth R L]

/-- **Base change of pinnings commutes with transport along isomorphisms**: base-changing the
transport of `P` along `e : H ≅ L` gives the transport of the base change of `P` along the base
change of `e`. -/
theorem baseChange_comapOfIso (P : Pinning R L r) (e : H ≅ L) :
    (P.comapOfIso e).baseChange S =
      (P.baseChange S).comapOfIso ((CommHopfAlgCat.baseChangeFunctor (K := S)).mapIso e) := by
  refine ext_rootVector ?_ ?_ fun α hP hQ ↦ ?_
  · rw [comapOfIso_torus, baseChange_torus, baseChange_torus, comapOfIso_torus,
      SplitMaximalTorus.baseChange_comapOfIso]
  · rw [comapOfIso_borel, baseChange_borel, baseChange_borel, comapOfIso_borel]
    exact CommHopfAlgCat.baseChangeHopfIdeal_comapOfIso P.borel e
  · rw [comapOfIso_rootVector, baseChange_rootVector, baseChange_rootVector,
      comapOfIso_rootVector, Functor.mapIso_hom, CommHopfAlgCat.baseChangeFunctor_map,
      CommHopfAlgCat.hom_baseChangeMap]
    exact (Derivation.dualCotangentMap_map_cotangentDualBaseChangeEquiv_tmul _ 1 _).symm

end Pinning

end TauCeti
