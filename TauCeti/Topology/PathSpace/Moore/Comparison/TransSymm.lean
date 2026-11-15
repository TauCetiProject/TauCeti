/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.PathSpace.Moore.Comparison.Trans
public import TauCeti.Topology.PathSpace.Moore.Between.Equiv

/-!
# Splitting a loop `p · q⁻¹` through a chosen path

Let `p` and `q` be paths on the unit interval from `x` to `y`, so that `p · q⁻¹` is a loop at `x`.
For any third path `r` from `x` to `y`, the loop `p · q⁻¹` is homotopic to
`(p · r⁻¹) · (r · q⁻¹)`: the inserted `r⁻¹ · r` cancels. This file proves the cancellation in the
Moore loop space, continuously in the pair `(p, q)`: the map
`(p, q) ↦ (p · q⁻¹)` (`Path.mooreLoopTransSymm`) is homotopic to the map
`(p, q) ↦ (p · r⁻¹) * (r · q⁻¹)` (`Path.mulMooreLoopVia r`), the product being the strict
concatenation of Moore loops (`Path.homotopic_mooreLoopTransSymm_mulMooreLoopVia`).

So a family of loops `p a · (q b)⁻¹`, `(a, b) ∈ A × B`, is, up to homotopy, the pointwise product
of the two families of loops `p a · r⁻¹` and `r · (q b)⁻¹`. On singular homology this turns the
class of the family into a Pontryagin product.

The proof works with Moore paths, whose concatenation is strictly associative. The Moore loop of
`p · q⁻¹` is homotopic to the concatenation of the Moore paths of `p` and `q⁻¹`
(`Path.transMoorePathHomotopy`), and likewise for the two factors of the product, which becomes
the concatenation of the Moore paths of `p`, `r⁻¹`, `r` and `q⁻¹`. The middle piece `r⁻¹ · r`
is inserted in front of `q⁻¹` by the retracting homotopy
`TauCeti.MoorePathBetween.prependSymmHomotopy`, which grows `r⁻¹ · r` from the constant path of
length zero.

## Main declarations

* `Path.mooreLoopTransSymm x y`: the Moore loop of `p · q⁻¹`, as a continuous map of `(p, q)`.
* `Path.mulMooreLoopVia r`: the product of the Moore loops of `p · r⁻¹` and `r · q⁻¹`.
* `Path.homotopic_mooreLoopTransSymm_mulMooreLoopVia`: the two are homotopic.

## References

* G. W. Whitehead, *Elements of Homotopy Theory*, GTM 61, Springer, 1978, Chapter III.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §6.4.2, proof of Proposition 6.17.
-/

public noncomputable section

open scoped NNReal unitInterval
open unitInterval

namespace Path

open TauCeti

variable {X : Type*} [TopologicalSpace X] {x y : X}

/-- The Moore loop of `p · q⁻¹` for two paths `p` and `q` from `x` to `y`, as a continuous map of
the pair. -/
def mooreLoopTransSymm (x y : X) : C(Path x y × Path x y, MooreLoopSpace X x) :=
  ⟨fun pq ↦ (pq.1.trans pq.2.symm).toMooreLoop,
    Path.continuous_toMooreLoop.comp
      (continuous_fst.path_trans (Path.continuous_symm.comp continuous_snd))⟩

@[simp]
theorem mooreLoopTransSymm_apply (pq : Path x y × Path x y) :
    mooreLoopTransSymm x y pq = (pq.1.trans pq.2.symm).toMooreLoop :=
  (rfl)

/-- The product of the Moore loops of `p · r⁻¹` and `r · q⁻¹`, for a fixed path `r` from `x` to `y`,
as a continuous map of the pair `(p, q)`. -/
def mulMooreLoopVia (r : Path x y) : C(Path x y × Path x y, MooreLoopSpace X x) :=
  ⟨fun pq ↦ (pq.1.trans r.symm).toMooreLoop * (r.trans pq.2.symm).toMooreLoop,
    (Path.continuous_toMooreLoop.comp (continuous_fst.path_trans continuous_const)).mul
      (Path.continuous_toMooreLoop.comp
        (continuous_const.path_trans (Path.continuous_symm.comp continuous_snd)))⟩

@[simp]
theorem mulMooreLoopVia_apply (r : Path x y) (pq : Path x y × Path x y) :
    mulMooreLoopVia r pq = (pq.1.trans r.symm).toMooreLoop * (r.trans pq.2.symm).toMooreLoop :=
  (rfl)

/-- The Moore loop of the concatenation of the Moore paths of `p` and `q⁻¹`. -/
private def transSymmMoorePath (x y : X) : C(Path x y × Path x y, MooreLoopSpace X x) :=
  ⟨fun pq ↦ ⟨pq.1.toMoorePath.trans pq.2.symm.toMoorePath (by simp), by simp, by simp⟩,
    MooreLoopSpace.isEmbedding_toMoorePath.continuous_iff.2 <|
      (Path.continuous_toMoorePath.comp continuous_fst).moorePath_trans
        (Path.continuous_toMoorePath.comp (Path.continuous_symm.comp continuous_snd))
        fun _ ↦ by simp⟩

/-- The Moore loop of `p · q⁻¹` is homotopic to the concatenation of the Moore paths of `p` and
`q⁻¹`, reparametrizing from length one to length two. -/
private def mooreLoopTransSymmHomotopy (x y : X) :
    ContinuousMap.Homotopy (mooreLoopTransSymm x y) (transSymmMoorePath x y) where
  toFun spq := ⟨transMoorePathHomotopy x y x (spq.1, (spq.2.1, spq.2.2.symm)), by simp, by simp⟩
  continuous_toFun := MooreLoopSpace.isEmbedding_toMoorePath.continuous_iff.2 <|
    (transMoorePathHomotopy x y x).continuous.comp
      (continuous_fst.prodMk (continuous_snd.fst.prodMk
        (Path.continuous_symm.comp continuous_snd.snd)))
  map_zero_left pq := MooreLoopSpace.ext <| by
    simp only [ContinuousMap.Homotopy.apply_zero, moorePathTrans_apply, mooreLoopTransSymm_apply,
      Path.toMoorePath_toMooreLoop]
  map_one_left pq := MooreLoopSpace.ext <| by
    simp only [ContinuousMap.Homotopy.apply_one, transMoorePath_apply, transSymmMoorePath,
      ContinuousMap.coe_mk]

/-- A path on the unit interval, as a Moore path between its end points. -/
private def toMoorePathBetween {a b : X} (p : Path a b) : MoorePathBetween X a b :=
  ⟨p.toMoorePath, by simp, by simp⟩

private theorem continuous_toMoorePathBetween {a b : X} :
    Continuous (toMoorePathBetween : Path a b → MoorePathBetween X a b) :=
  Path.continuous_toMoorePath.subtype_mk _

/-- The Moore loop of the concatenation of the Moore paths of `p`, `r⁻¹`, `r` and `q⁻¹`. -/
private def cancelMoorePath (r : Path x y) : C(Path x y × Path x y, MooreLoopSpace X x) :=
  ⟨fun pq ↦ ⟨pq.1.toMoorePath.trans (r.symm.toMoorePath.trans
      (r.toMoorePath.trans pq.2.symm.toMoorePath (by simp)) (by simp)) (by simp), by simp, by simp⟩,
    MooreLoopSpace.isEmbedding_toMoorePath.continuous_iff.2 <|
      (Path.continuous_toMoorePath.comp continuous_fst).moorePath_trans
        (continuous_const.moorePath_trans (continuous_const.moorePath_trans
          (Path.continuous_toMoorePath.comp (Path.continuous_symm.comp continuous_snd))
          fun _ ↦ by simp) fun _ ↦ by simp) fun _ ↦ by simp⟩

/-- Inserting `r⁻¹ · r` between the Moore paths of `p` and `q⁻¹`: the retracing homotopy
`MoorePathBetween.prependSymmHomotopy` of `r⁻¹`, acting on the Moore path of `q⁻¹`. -/
private def cancelHomotopy (r : Path x y) :
    ContinuousMap.Homotopy (transSymmMoorePath x y) (cancelMoorePath r) where
  toFun spq := (MoorePathBetween.loopHomeomorph x).symm ((toMoorePathBetween spq.2.1).trans
    (MoorePathBetween.prependSymmHomotopy (toMoorePathBetween r.symm) x
      (spq.1, toMoorePathBetween spq.2.2.symm)))
  continuous_toFun := (MoorePathBetween.loopHomeomorph x).symm.continuous.comp <|
    MoorePathBetween.continuous_trans.comp
      ((continuous_toMoorePathBetween.comp continuous_snd.fst).prodMk
        ((MoorePathBetween.prependSymmHomotopy _ x).continuous.comp (continuous_fst.prodMk
          (continuous_toMoorePathBetween.comp (Path.continuous_symm.comp continuous_snd.snd)))))
  map_zero_left pq := by
    simp only [ContinuousMap.Homotopy.apply_zero, ContinuousMap.id_apply]
    exact MooreLoopSpace.ext (by simp [transSymmMoorePath, toMoorePathBetween])
  map_one_left pq := by
    simp only [ContinuousMap.Homotopy.apply_one, ContinuousMap.comp_apply,
      MoorePathBetween.prepend_apply]
    exact MooreLoopSpace.ext (by simp [cancelMoorePath, toMoorePathBetween])

/-- The product of the Moore loops of `p · r⁻¹` and `r · q⁻¹` is homotopic to the concatenation of
the Moore paths of `p`, `r⁻¹`, `r` and `q⁻¹`, reparametrizing each factor from length one to
length two. -/
private def mulMooreLoopViaHomotopy (r : Path x y) :
    ContinuousMap.Homotopy (mulMooreLoopVia r) (cancelMoorePath r) where
  toFun spq := ⟨(transMoorePathHomotopy x y x (spq.1, (spq.2.1, r.symm))).trans
    (transMoorePathHomotopy x y x (spq.1, (r, spq.2.2.symm))) (by simp), by simp, by simp⟩
  continuous_toFun := MooreLoopSpace.isEmbedding_toMoorePath.continuous_iff.2 <|
    ((transMoorePathHomotopy x y x).continuous.comp
      (continuous_fst.prodMk (continuous_snd.fst.prodMk continuous_const))).moorePath_trans
      ((transMoorePathHomotopy x y x).continuous.comp
        (continuous_fst.prodMk (continuous_const.prodMk
          (Path.continuous_symm.comp continuous_snd.snd)))) fun _ ↦ by simp
  map_zero_left pq := MooreLoopSpace.ext <| by
    simp only [ContinuousMap.Homotopy.apply_zero, moorePathTrans_apply, mulMooreLoopVia_apply,
      MooreLoopSpace.toMoorePath_mul, Path.toMoorePath_toMooreLoop]
  map_one_left pq := MooreLoopSpace.ext <| by
    simp only [ContinuousMap.Homotopy.apply_one, transMoorePath_apply, cancelMoorePath,
      ContinuousMap.coe_mk]
    exact MoorePath.trans_assoc _ _ _ _ _

/-- **Cancellation through a chosen path.** For a path `r` from `x` to `y`, the Moore loop of
`p · q⁻¹` is homotopic to the product of the Moore loops of `p · r⁻¹` and `r · q⁻¹`, continuously
in the pair `(p, q)` of paths from `x` to `y`. -/
theorem homotopic_mooreLoopTransSymm_mulMooreLoopVia (r : Path x y) :
    (mooreLoopTransSymm x y).Homotopic (mulMooreLoopVia r) :=
  ⟨(mooreLoopTransSymmHomotopy x y).trans
    ((cancelHomotopy r).trans (mulMooreLoopViaHomotopy r).symm)⟩

end Path
