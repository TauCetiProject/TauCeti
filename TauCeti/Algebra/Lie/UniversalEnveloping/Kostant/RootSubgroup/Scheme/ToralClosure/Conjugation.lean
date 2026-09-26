/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Conjugation
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Equivalence
public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Scheme.ToralClosure.Points

/-!
# Conjugating the toral Kostant closure by a constant matrix

The toral Kostant closure is the smallest closed subgroup scheme of `GLₙ` over `ℤ` containing the
represented Kostant root subgroups and the represented weight torus. Its points therefore satisfy
a universal property with respect to every closed subgroup scheme `Z ≤ GLₙ` and every
automorphism of `GLₙ`: if an automorphism carries each generator into `Z`, it carries the whole
closure into `Z`. This file records that property for conjugation by a constant invertible integral
matrix `P`, in its algebra-valued form: if

```text
P xᵢ(t) P⁻¹ ∈ Z(A)    and    P d(s) P⁻¹ ∈ Z(A)
```

for every root subgroup `xᵢ`, every torus point `d(s)`, and every ring `A`, then `P g P⁻¹ ∈ Z(A)`
for every point `g` of the toral closure over every ring `A`.

Taking `Z` to be a second toral Kostant closure compares two explicit carriers built from
different representations: a change of basis carrying the generators of one into the other
carries all points, and a change of basis matching the generators in both directions identifies
the two point groups over every ring. This recognises one explicit carrier as another carrier of
the same diagram without passing through any statement about the underlying abstract group.

## Main results

* `comapOfSurjective_conjCoordinateIso_inv_le_kostantToralDefiningIdeal` and
  `conj_mem_hopfIdealPointsSubgroup_of_mem_kostantToralPointsSubgroup`: the universal property
  above, for an arbitrary closed subgroup scheme of `GLₙ`, on defining ideals and on points.
* `map_conj_kostantToralPointsSubgroup_le`: conjugation by `P` maps the points of one toral closure
  into those of a second when it maps its generators there.
* `map_reindex_conj_kostantToralPointsSubgroup_eq` and `kostantToralPointsReindexConjMulEquiv`:
  when in addition the inverse operation maps the generators of the second closure into the first,
  reindexing along `finCongr` followed by conjugation identifies the two point groups over every
  ring. The reindexing lets the two carriers have matrix sizes that agree only propositionally.

All of these live in the `TauCeti.UniversalEnvelopingAlgebra` namespace.

## References

The toral closure is the carrier of the Chevalley--Demazure construction assembled from the root
subgroups and a split torus; see J. E. Humphreys, *Linear Algebraic Groups*, §§7.5 and 26, and
R. W. Carter, *Simple Groups of Lie Type*, §§4.4 and 7.1.
-/

public section

open CategoryTheory TensorProduct WithConv

namespace TauCeti.UniversalEnvelopingAlgebra

universe u u' v w w'

-- Match tensor products to the `ℤ`-algebra structure used by scalar extension.
attribute [local instance high] Algebra.toModule

variable {L : Type u} [LieRing L] [LieAlgebra ℚ L]
variable {I : Type w} {κ : Type} [Fintype κ]
variable {V : Type} [AddCommGroup V] [Module ℚ V]

variable (e : I → L) (h : κ → L)
variable (ρ : _root_.UniversalEnvelopingAlgebra ℚ L →ₐ[ℚ] Module.End ℚ V)
variable (M : AddSubgroup V)
variable (hM : ∀ u ∈ kostantForm e h, ∀ m ∈ M, ρ u m ∈ M)
variable (hnil : ∀ i, IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i))))
variable {n : ℕ} (b : Module.Basis (Fin n) ℤ M)
variable (wt : Fin n → κ → ℤ)

section UniversalProperty

variable (J : HopfIdeal ℤ (GeneralLinear.coordinateHopfAlgebra ℤ n))
variable (P : Matrix.GeneralLinearGroup (Fin n) ℤ)

/-- If a point of `GLₙ` over `A` is conjugated by `P` into the subgroup cut out by `J`, then
precomposing it with the coordinate automorphism of conjugation by `P` kills `J`. -/
private theorem ofConv_conjCoordinateIso_hom_eq_zero (A : Type) [CommRing A]
    (f : WithConv (GeneralLinear.coordinateHopfAlgebra ℤ n →ₐ[ℤ] A))
    (hf : Matrix.GeneralLinearGroup.map (algebraMap ℤ A) P * GeneralLinear.pointsMulEquiv n f *
        (Matrix.GeneralLinearGroup.map (algebraMap ℤ A) P)⁻¹ ∈
      GeneralLinear.hopfIdealPointsSubgroup n J A)
    {x : GeneralLinear.coordinateHopfAlgebra ℤ n} (hx : x ∈ J) :
    f.ofConv ((GeneralLinear.conjCoordinateIso P).hom.hom x) = 0 := by
  rw [← GeneralLinear.pointsMulEquiv_toConv_comp_conjCoordinateIso,
    GeneralLinear.mem_hopfIdealPointsSubgroup_iff, MulEquiv.symm_apply_apply] at hf
  exact hf x hx

/-- **Conjugating the generators into a Hopf ideal quotient pulls that ideal into the toral defining
ideal.** If conjugation by `P` carries every represented root subgroup point and every represented
weight-torus point into the closed subgroup scheme cut out by `J`, then the image of `J` under the
coordinate automorphism of conjugation by `P` lies in the defining ideal of the toral closure. -/
theorem comapOfSurjective_conjCoordinateIso_inv_le_kostantToralDefiningIdeal
    (hroot : ∀ (A : Type) [CommRing A] (i : I)
      (q : WithConv (AdditiveGroup.coordinateHopfAlgebra ℤ →ₐ[ℤ] A)),
      Matrix.GeneralLinearGroup.map (algebraMap ℤ A) P *
          kostantRootSubgroupMatrix e h ρ M hM i (hnil i) b q *
          (Matrix.GeneralLinearGroup.map (algebraMap ℤ A) P)⁻¹ ∈
        GeneralLinear.hopfIdealPointsSubgroup n J A)
    (htorus : ∀ (A : Type) [CommRing A] (s : κ → Aˣ),
      Matrix.GeneralLinearGroup.map (algebraMap ℤ A) P * kostantTorusMatrix M b wt s *
          (Matrix.GeneralLinearGroup.map (algebraMap ℤ A) P)⁻¹ ∈
        GeneralLinear.hopfIdealPointsSubgroup n J A) :
    J.comapOfSurjective (GeneralLinear.conjCoordinateIso P).inv.hom
        (ConcreteCategory.bijective_of_isIso (GeneralLinear.conjCoordinateIso P).inv).2 ≤
      kostantToralDefiningIdeal e h ρ M hM hnil b wt := by
  let c := GeneralLinear.conjCoordinateIso (R := ℤ) P
  -- Every coordinate is the image under `c` of its preimage under `c`.
  have hc (y : GeneralLinear.coordinateHopfAlgebra ℤ n) : c.hom.hom (c.inv.hom y) = y := by
    rw [← _root_.CommHopfAlgCat.comp_apply, Iso.inv_hom_id, _root_.CommHopfAlgCat.id_apply]
  rw [le_kostantToralDefiningIdeal_iff]
  refine ⟨fun i y hy => ?_, fun y hy => ?_⟩
  · -- Evaluate at the generic point of `𝔾ₐ`, where the root coordinate map is its own matrix.
    let r := kostantRootSubgroupCoordinateMap e h ρ M hM i (hnil i) b
    let q : WithConv (AdditiveGroup.coordinateHopfAlgebra ℤ →ₐ[ℤ]
        AdditiveGroup.coordinateHopfAlgebra ℤ) := toConv (AlgHom.id ℤ _)
    let f : WithConv (GeneralLinear.coordinateHopfAlgebra ℤ n →ₐ[ℤ]
        AdditiveGroup.coordinateHopfAlgebra ℤ) := toConv (q.ofConv.comp r.hom)
    have hmatrix : GeneralLinear.pointsMulEquiv n f =
        kostantRootSubgroupMatrix e h ρ M hM i (hnil i) b q := by
      rw [GeneralLinear.pointsMulEquiv_apply]
      exact pointsMulEquiv_kostantRootSubgroupCoordinateMap e h ρ M hM i (hnil i) b _ q
    have hzero := ofConv_conjCoordinateIso_hom_eq_zero J P _ f
      (hmatrix ▸ hroot _ i q) (HopfIdeal.mem_comapOfSurjective.mp hy)
    rw [hc] at hzero
    exact hzero
  · -- Evaluate at the generic point of the split torus.
    let t := GeneralLinear.weightTorusCoordinateMap (R := ℤ) wt
    let p : HopfAlgebra.points (R := ℤ)
        (H := MonoidAlgebra ℤ (SplitTorus.characterGroup κ))
        (CommAlgCat.of ℤ (MonoidAlgebra ℤ (SplitTorus.characterGroup κ))) :=
      toConv (AlgHom.id ℤ _)
    let f : WithConv (GeneralLinear.coordinateHopfAlgebra ℤ n →ₐ[ℤ]
        MonoidAlgebra ℤ (SplitTorus.characterGroup κ)) :=
      (CommHopfAlgCat.mapPointsFunctor t).app _ p
    have hmatrix : GeneralLinear.pointsMulEquiv n f =
        kostantTorusMatrix M b wt (SplitTorus.pointsMulEquiv p) := by
      rw [kostantTorusMatrix_apply]
      exact GeneralLinear.pointsMulEquiv_mapPointsFunctor_weightTorusCoordinateMap wt _ p
    have hzero := ofConv_conjCoordinateIso_hom_eq_zero J P _ f
      (hmatrix ▸ htorus _ _) (HopfIdeal.mem_comapOfSurjective.mp hy)
    rw [hc] at hzero
    exact hzero

/-- **The toral closure is carried into every closed subgroup scheme into which conjugation by `P`
carries its generators.** -/
theorem conj_mem_hopfIdealPointsSubgroup_of_mem_kostantToralPointsSubgroup
    (hroot : ∀ (A : Type) [CommRing A] (i : I)
      (q : WithConv (AdditiveGroup.coordinateHopfAlgebra ℤ →ₐ[ℤ] A)),
      Matrix.GeneralLinearGroup.map (algebraMap ℤ A) P *
          kostantRootSubgroupMatrix e h ρ M hM i (hnil i) b q *
          (Matrix.GeneralLinearGroup.map (algebraMap ℤ A) P)⁻¹ ∈
        GeneralLinear.hopfIdealPointsSubgroup n J A)
    (htorus : ∀ (A : Type) [CommRing A] (s : κ → Aˣ),
      Matrix.GeneralLinearGroup.map (algebraMap ℤ A) P * kostantTorusMatrix M b wt s *
          (Matrix.GeneralLinearGroup.map (algebraMap ℤ A) P)⁻¹ ∈
        GeneralLinear.hopfIdealPointsSubgroup n J A)
    (A : Type v) [CommRing A] {g : Matrix.GeneralLinearGroup (Fin n) A}
    (hg : g ∈ kostantToralPointsSubgroup e h ρ M hM hnil b wt A) :
    Matrix.GeneralLinearGroup.map (algebraMap ℤ A) P * g *
        (Matrix.GeneralLinearGroup.map (algebraMap ℤ A) P)⁻¹ ∈
      GeneralLinear.hopfIdealPointsSubgroup n J A := by
  let c := GeneralLinear.conjCoordinateIso (R := ℤ) P
  have hle := comapOfSurjective_conjCoordinateIso_inv_le_kostantToralDefiningIdeal
    e h ρ M hM hnil b wt J P hroot htorus
  rw [mem_kostantToralPointsSubgroup_iff] at hg
  rw [← MulEquiv.apply_symm_apply (GeneralLinear.pointsMulEquiv (R := ℤ) (A := A) n) g,
    ← GeneralLinear.pointsMulEquiv_toConv_comp_conjCoordinateIso,
    GeneralLinear.mem_hopfIdealPointsSubgroup_iff, MulEquiv.symm_apply_apply]
  intro x hx
  -- The coordinate `c x` lies in the toral defining ideal, since `c⁻¹ (c x) = x ∈ J`.
  have hcx : c.hom.hom x ∈ kostantToralDefiningIdeal e h ρ M hM hnil b wt := by
    apply hle
    rw [HopfIdeal.mem_comapOfSurjective, ← _root_.CommHopfAlgCat.comp_apply, Iso.hom_inv_id,
      _root_.CommHopfAlgCat.id_apply]
    exact hx
  exact hg _ hcx

end UniversalProperty

section TwoCarriers

variable {L' : Type u'} [LieRing L'] [LieAlgebra ℚ L']
variable {I' : Type w'} {κ' : Type} [Finite κ']
variable {V' : Type} [AddCommGroup V'] [Module ℚ V']

variable (e' : I' → L') (h' : κ' → L')
variable (ρ' : _root_.UniversalEnvelopingAlgebra ℚ L' →ₐ[ℚ] Module.End ℚ V')
variable (M' : AddSubgroup V')
variable (hM' : ∀ u ∈ kostantForm e' h', ∀ m ∈ M', ρ' u m ∈ M')
variable (hnil' : ∀ i, IsNilpotent (ρ' (_root_.UniversalEnvelopingAlgebra.ι ℚ (e' i))))
variable (b' : Module.Basis (Fin n) ℤ M')
variable (wt' : Fin n → κ' → ℤ)

variable (P : Matrix.GeneralLinearGroup (Fin n) ℤ)

/-- **Conjugation by `P` maps the points of one toral closure into those of a second** as soon as
it maps the generating root subgroup and weight-torus points of the first into the second. -/
theorem map_conj_kostantToralPointsSubgroup_le
    (hroot : ∀ (A : Type) [CommRing A] (i : I)
      (q : WithConv (AdditiveGroup.coordinateHopfAlgebra ℤ →ₐ[ℤ] A)),
      Matrix.GeneralLinearGroup.map (algebraMap ℤ A) P *
          kostantRootSubgroupMatrix e h ρ M hM i (hnil i) b q *
          (Matrix.GeneralLinearGroup.map (algebraMap ℤ A) P)⁻¹ ∈
        kostantToralPointsSubgroup e' h' ρ' M' hM' hnil' b' wt' A)
    (htorus : ∀ (A : Type) [CommRing A] (s : κ → Aˣ),
      Matrix.GeneralLinearGroup.map (algebraMap ℤ A) P * kostantTorusMatrix M b wt s *
          (Matrix.GeneralLinearGroup.map (algebraMap ℤ A) P)⁻¹ ∈
        kostantToralPointsSubgroup e' h' ρ' M' hM' hnil' b' wt' A)
    (A : Type v) [CommRing A] :
    (kostantToralPointsSubgroup e h ρ M hM hnil b wt A).map
        (MulAut.conj (Matrix.GeneralLinearGroup.map (algebraMap ℤ A) P)).toMonoidHom ≤
      kostantToralPointsSubgroup e' h' ρ' M' hM' hnil' b' wt' A := by
  rintro _ ⟨g, hg, rfl⟩
  simp only [kostantToralPointsSubgroup_def] at hroot htorus ⊢
  exact conj_mem_hopfIdealPointsSubgroup_of_mem_kostantToralPointsSubgroup
    e h ρ M hM hnil b wt _ P hroot htorus A hg

/-! ### Carriers of propositionally equal size

The matrix size of a toral closure is the rank of its lattice, which for a concrete carrier is often
a closed-form expression, such as the cardinality of an index set, that equals the size of a second
carrier only after computation. The comparison below therefore allows the second carrier to live in
`GLₙ'` for some `n'` with `n = n'`, and reindexes along `finCongr` before conjugating. -/

variable {n' : ℕ} (hn : n = n') (b'' : Module.Basis (Fin n') ℤ M') (wt'' : Fin n' → κ' → ℤ)
variable (Q : Matrix.GeneralLinearGroup (Fin n') ℤ)

/-- **Conjugation by `Q` after reindexing identifies the points of two toral closures** when it
maps the generators of the first into the second and the inverse operation maps the generators of
the second into the first. -/
theorem map_reindex_conj_kostantToralPointsSubgroup_eq [Fintype κ']
    (hroot : ∀ (A : Type) [CommRing A] (i : I)
      (q : WithConv (AdditiveGroup.coordinateHopfAlgebra ℤ →ₐ[ℤ] A)),
      Matrix.GeneralLinearGroup.map (algebraMap ℤ A) Q *
          (finCongr hn).reindexGL A (kostantRootSubgroupMatrix e h ρ M hM i (hnil i) b q) *
          (Matrix.GeneralLinearGroup.map (algebraMap ℤ A) Q)⁻¹ ∈
        kostantToralPointsSubgroup e' h' ρ' M' hM' hnil' b'' wt'' A)
    (htorus : ∀ (A : Type) [CommRing A] (s : κ → Aˣ),
      Matrix.GeneralLinearGroup.map (algebraMap ℤ A) Q *
          (finCongr hn).reindexGL A (kostantTorusMatrix M b wt s) *
          (Matrix.GeneralLinearGroup.map (algebraMap ℤ A) Q)⁻¹ ∈
        kostantToralPointsSubgroup e' h' ρ' M' hM' hnil' b'' wt'' A)
    (hroot' : ∀ (A : Type) [CommRing A] (i : I')
      (q : WithConv (AdditiveGroup.coordinateHopfAlgebra ℤ →ₐ[ℤ] A)),
      (finCongr hn).symm.reindexGL A ((Matrix.GeneralLinearGroup.map (algebraMap ℤ A) Q)⁻¹ *
          kostantRootSubgroupMatrix e' h' ρ' M' hM' i (hnil' i) b'' q *
          Matrix.GeneralLinearGroup.map (algebraMap ℤ A) Q) ∈
        kostantToralPointsSubgroup e h ρ M hM hnil b wt A)
    (htorus' : ∀ (A : Type) [CommRing A] (s : κ' → Aˣ),
      (finCongr hn).symm.reindexGL A ((Matrix.GeneralLinearGroup.map (algebraMap ℤ A) Q)⁻¹ *
          kostantTorusMatrix M' b'' wt'' s * Matrix.GeneralLinearGroup.map (algebraMap ℤ A) Q) ∈
        kostantToralPointsSubgroup e h ρ M hM hnil b wt A)
    (A : Type v) [CommRing A] :
    (kostantToralPointsSubgroup e h ρ M hM hnil b wt A).map
        ((MulAut.conj (Matrix.GeneralLinearGroup.map (algebraMap ℤ A) Q)).toMonoidHom.comp
          ((finCongr hn).reindexGL A).toMonoidHom) =
      kostantToralPointsSubgroup e' h' ρ' M' hM' hnil' b'' wt'' A := by
  subst hn
  simp only [finCongr_refl, Equiv.refl_symm, Equiv.reindexGL_refl, MulEquiv.refl_apply]
    at hroot htorus hroot' htorus' ⊢
  refine le_antisymm ?_ fun g hg => ?_
  · rintro _ ⟨g, hg, rfl⟩
    exact map_conj_kostantToralPointsSubgroup_le e h ρ M hM hnil b wt e' h' ρ' M' hM' hnil' b''
      wt'' Q hroot htorus A ⟨g, hg, rfl⟩
  · have hback := map_conj_kostantToralPointsSubgroup_le e' h' ρ' M' hM' hnil' b'' wt''
      e h ρ M hM hnil b wt Q⁻¹
      (fun B _ i q => by simpa only [map_inv, inv_inv] using hroot' B i q)
      (fun B _ s => by simpa only [map_inv, inv_inv] using htorus' B s) A ⟨g, hg, rfl⟩
    refine ⟨_, hback, ?_⟩
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.refl_apply,
      MulAut.conj_apply, map_inv (Matrix.GeneralLinearGroup.map (algebraMap ℤ A)) Q, inv_inv]
    group

/-- **The identification of the points of two toral closures by reindexing and conjugating by
`Q`.** -/
noncomputable def kostantToralPointsReindexConjMulEquiv [Fintype κ']
    (hroot : ∀ (A : Type) [CommRing A] (i : I)
      (q : WithConv (AdditiveGroup.coordinateHopfAlgebra ℤ →ₐ[ℤ] A)),
      Matrix.GeneralLinearGroup.map (algebraMap ℤ A) Q *
          (finCongr hn).reindexGL A (kostantRootSubgroupMatrix e h ρ M hM i (hnil i) b q) *
          (Matrix.GeneralLinearGroup.map (algebraMap ℤ A) Q)⁻¹ ∈
        kostantToralPointsSubgroup e' h' ρ' M' hM' hnil' b'' wt'' A)
    (htorus : ∀ (A : Type) [CommRing A] (s : κ → Aˣ),
      Matrix.GeneralLinearGroup.map (algebraMap ℤ A) Q *
          (finCongr hn).reindexGL A (kostantTorusMatrix M b wt s) *
          (Matrix.GeneralLinearGroup.map (algebraMap ℤ A) Q)⁻¹ ∈
        kostantToralPointsSubgroup e' h' ρ' M' hM' hnil' b'' wt'' A)
    (hroot' : ∀ (A : Type) [CommRing A] (i : I')
      (q : WithConv (AdditiveGroup.coordinateHopfAlgebra ℤ →ₐ[ℤ] A)),
      (finCongr hn).symm.reindexGL A ((Matrix.GeneralLinearGroup.map (algebraMap ℤ A) Q)⁻¹ *
          kostantRootSubgroupMatrix e' h' ρ' M' hM' i (hnil' i) b'' q *
          Matrix.GeneralLinearGroup.map (algebraMap ℤ A) Q) ∈
        kostantToralPointsSubgroup e h ρ M hM hnil b wt A)
    (htorus' : ∀ (A : Type) [CommRing A] (s : κ' → Aˣ),
      (finCongr hn).symm.reindexGL A ((Matrix.GeneralLinearGroup.map (algebraMap ℤ A) Q)⁻¹ *
          kostantTorusMatrix M' b'' wt'' s * Matrix.GeneralLinearGroup.map (algebraMap ℤ A) Q) ∈
        kostantToralPointsSubgroup e h ρ M hM hnil b wt A)
    (A : Type v) [CommRing A] :
    kostantToralPointsSubgroup e h ρ M hM hnil b wt A ≃*
      kostantToralPointsSubgroup e' h' ρ' M' hM' hnil' b'' wt'' A :=
  (MulEquiv.subgroupMap (((finCongr hn).reindexGL A).trans
      (MulAut.conj (Matrix.GeneralLinearGroup.map (algebraMap ℤ A) Q)))
      (kostantToralPointsSubgroup e h ρ M hM hnil b wt A)).trans
    (MulEquiv.subgroupCongr (map_reindex_conj_kostantToralPointsSubgroup_eq e h ρ M hM hnil b wt
      e' h' ρ' M' hM' hnil' hn b'' wt'' Q hroot htorus hroot' htorus' A))

/-- The identification of two toral closures reindexes and then conjugates by `Q`. -/
@[simp]
theorem coe_kostantToralPointsReindexConjMulEquiv_apply [Fintype κ']
    (hroot : ∀ (A : Type) [CommRing A] (i : I)
      (q : WithConv (AdditiveGroup.coordinateHopfAlgebra ℤ →ₐ[ℤ] A)),
      Matrix.GeneralLinearGroup.map (algebraMap ℤ A) Q *
          (finCongr hn).reindexGL A (kostantRootSubgroupMatrix e h ρ M hM i (hnil i) b q) *
          (Matrix.GeneralLinearGroup.map (algebraMap ℤ A) Q)⁻¹ ∈
        kostantToralPointsSubgroup e' h' ρ' M' hM' hnil' b'' wt'' A)
    (htorus : ∀ (A : Type) [CommRing A] (s : κ → Aˣ),
      Matrix.GeneralLinearGroup.map (algebraMap ℤ A) Q *
          (finCongr hn).reindexGL A (kostantTorusMatrix M b wt s) *
          (Matrix.GeneralLinearGroup.map (algebraMap ℤ A) Q)⁻¹ ∈
        kostantToralPointsSubgroup e' h' ρ' M' hM' hnil' b'' wt'' A)
    (hroot' : ∀ (A : Type) [CommRing A] (i : I')
      (q : WithConv (AdditiveGroup.coordinateHopfAlgebra ℤ →ₐ[ℤ] A)),
      (finCongr hn).symm.reindexGL A ((Matrix.GeneralLinearGroup.map (algebraMap ℤ A) Q)⁻¹ *
          kostantRootSubgroupMatrix e' h' ρ' M' hM' i (hnil' i) b'' q *
          Matrix.GeneralLinearGroup.map (algebraMap ℤ A) Q) ∈
        kostantToralPointsSubgroup e h ρ M hM hnil b wt A)
    (htorus' : ∀ (A : Type) [CommRing A] (s : κ' → Aˣ),
      (finCongr hn).symm.reindexGL A ((Matrix.GeneralLinearGroup.map (algebraMap ℤ A) Q)⁻¹ *
          kostantTorusMatrix M' b'' wt'' s * Matrix.GeneralLinearGroup.map (algebraMap ℤ A) Q) ∈
        kostantToralPointsSubgroup e h ρ M hM hnil b wt A)
    (A : Type v) [CommRing A] (g : kostantToralPointsSubgroup e h ρ M hM hnil b wt A) :
    (kostantToralPointsReindexConjMulEquiv e h ρ M hM hnil b wt e' h' ρ' M' hM' hnil' hn b''
        wt'' Q hroot htorus hroot' htorus' A g : Matrix.GeneralLinearGroup (Fin n') A) =
      Matrix.GeneralLinearGroup.map (algebraMap ℤ A) Q * (finCongr hn).reindexGL A g *
        (Matrix.GeneralLinearGroup.map (algebraMap ℤ A) Q)⁻¹ := by
  rw [kostantToralPointsReindexConjMulEquiv]
  rfl

end TwoCarriers

end TauCeti.UniversalEnvelopingAlgebra
