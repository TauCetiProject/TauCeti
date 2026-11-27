/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.FormalGroup.Module.Basic
public import TauCeti.RingTheory.FormalGroup.TopNilpotentPoint.Ideal
public import TauCeti.RingTheory.FormalGroup.TopNilpotentPoint.Topology
public import Mathlib.Topology.Algebra.Module.Equiv.Basic
import Mathlib.Algebra.Module.MinimalAxioms

/-!
# Evaluated points of a formal module

For a formal `A`-module `ρ` on a law `F`, evaluating the scalar series `[a]` makes the
topologically nilpotent points over a complete Hausdorff linearly topologized coefficient
algebra `S` into an `A`-module. Use `letI := ρ.isComm` and
`letI := ρ.topNilpotentPointModule S` to work with this action on the native point group.

The submodule `ρ.idealPointSubmodule I` consists of the points with coordinate in `I`.
In particular, if all elements of `I` are topologically nilpotent, its coordinates range
over precisely `I`. Formal-module homomorphisms and continuous coefficient algebra maps
sending the source ideal into the target ideal induce continuous linear maps on ideal points.
A formal-group isomorphism intertwining the scalar actions induces a continuous linear
equivalence. In particular, a change of coordinate gives this equivalence when the target
carries the transported action.

## References

* J. Lubin and J. Tate, *Formal complex multiplication in local fields*, §1, (12)–(13).
-/

public section

noncomputable section

namespace TauCeti.FormalModule

open FormalGroup

variable {A R : Type*} [CommRing A] [CommRing R] [Algebra A R] {F G : FormalGroup R}
variable (ρ : FormalModule A F)
variable {S : Type*} [CommRing S] [Algebra R S] [UniformSpace S] [IsUniformAddGroup S]
  [CompleteSpace S] [T2Space S] [IsTopologicalRing S] [IsLinearTopology S S]

/-- Evaluating the formal sum of scalar endomorphisms gives addition in the point group. -/
theorem toTopNilpotentPointHom_act_add (a b : A) (x : F.TopNilpotentPoint S) :
    (ρ.act (a + b)).toTopNilpotentPointHom S x =
      (ρ.act a).toTopNilpotentPointHom S x + (ρ.act b).toTopNilpotentPointHom S x := by
  let _ : UniformSpace R := ⊥
  apply TopNilpotentPoint.ext
  simp only [TopNilpotentPoint.val_add_eq_eval₂, FormalGroupHom.val_toTopNilpotentPointHom,
    ρ.act_add, PowerSeries.eval₂]
  exact MvPowerSeries.eval₂_subst_finTwo (ρ.act a).hasSubst (ρ.act b).hasSubst
    (PowerSeries.hasEval x.hasEval) F.toPowerSeries

variable (S) in
/-- The module structure on convergent points, with `a • x = [a](x)`. -/
@[instance_reducible]
def topNilpotentPointModule :
    letI := ρ.isComm
    Module A (F.TopNilpotentPoint S) :=
  letI := ρ.isComm
  letI action : SMul A (F.TopNilpotentPoint S) := ⟨fun a ↦ (ρ.act a).toTopNilpotentPointHom S⟩
  Module.ofMinimalAxioms (fun a ↦ map_add ((ρ.act a).toTopNilpotentPointHom S))
    ρ.toTopNilpotentPointHom_act_add
    (fun a b x ↦ by simp [HSMul.hSMul, SMul.smul, action, ρ.act_mul])
    (fun x ↦ by simp [HSMul.hSMul, SMul.smul, action])

/-- Scalar multiplication on a convergent point evaluates the scalar endomorphism. -/
@[simp]
theorem smul_topNilpotentPoint (a : A) (x : F.TopNilpotentPoint S) :
    letI := ρ.isComm
    letI := ρ.topNilpotentPointModule S
    a • x = (ρ.act a).toTopNilpotentPointHom S x := (rfl)

/-- The submodule of convergent points whose coordinates belong to `I`. -/
def idealPointSubmodule (I : Ideal S) :
    letI := ρ.isComm
    letI := ρ.topNilpotentPointModule S
    Submodule A (F.TopNilpotentPoint S) :=
  letI := ρ.isComm
  letI := ρ.topNilpotentPointModule S
  { F.idealPointSubgroup I with
    smul_mem' := fun a x hx ↦ by
      rw [smul_topNilpotentPoint]
      exact (F.mem_idealPointSubgroup I _).2 <|
        (ρ.act a).val_toTopNilpotentPointHom_mem I ((F.mem_idealPointSubgroup I x).1 hx) }

@[simp]
theorem mem_idealPointSubmodule (I : Ideal S) (x : F.TopNilpotentPoint S) :
    x ∈ ρ.idealPointSubmodule I ↔ x.val ∈ I := F.mem_idealPointSubgroup I x

/-- Two points in the ideal submodule are equal exactly when their coordinates agree. -/
theorem idealPointSubmodule_eq_iff {I : Ideal S} {x y : ρ.idealPointSubmodule I} :
    x = y ↔ x.val.val = y.val.val := FormalGroup.idealPointSubgroup_eq_iff

@[simp]
theorem idealPointSubmodule_toAddSubgroup (I : Ideal S) :
    letI := ρ.isComm
    (ρ.idealPointSubmodule I).toAddSubgroup = F.idealPointSubgroup I := (rfl)

/-- The zero ideal cuts out just the zero point. -/
@[simp]
theorem idealPointSubmodule_bot :
    letI := ρ.isComm
    letI := ρ.topNilpotentPointModule S
    ρ.idealPointSubmodule (⊥ : Ideal S) = ⊥ := by
  let _ := ρ.isComm
  let _ := ρ.topNilpotentPointModule S
  ext x
  rw [mem_idealPointSubmodule, Submodule.mem_bot, Submodule.mem_bot]
  exact ⟨fun hx ↦ TopNilpotentPoint.ext hx, fun hx ↦ hx ▸ TopNilpotentPoint.val_zero F⟩

/-- All convergent points have coordinate in the unit ideal. -/
@[simp]
theorem idealPointSubmodule_top :
    letI := ρ.isComm
    letI := ρ.topNilpotentPointModule S
    ρ.idealPointSubmodule (⊤ : Ideal S) = ⊤ := by
  let _ := ρ.isComm
  let _ := ρ.topNilpotentPointModule S
  ext
  simp

section Coefficients

variable {T U : Type*} [CommRing T] [Algebra R T] [UniformSpace T] [IsUniformAddGroup T]
  [CompleteSpace T] [T2Space T] [IsTopologicalRing T] [IsLinearTopology T T]
  [CommRing U] [Algebra R U] [UniformSpace U] [IsUniformAddGroup U]
  [CompleteSpace U] [T2Space U] [IsTopologicalRing U] [IsLinearTopology U U]

/-- A continuous algebra map acts continuously and linearly on convergent points. -/
def mapTopNilpotentPoint (φ : S →A[R] T) :
    letI := ρ.isComm
    letI := ρ.topNilpotentPointModule S
    letI := ρ.topNilpotentPointModule T
    F.TopNilpotentPoint S →L[A] F.TopNilpotentPoint T :=
  letI := ρ.isComm
  letI := ρ.topNilpotentPointModule S
  letI := ρ.topNilpotentPointModule T
  { TopNilpotentPoint.map F φ with
    map_smul' := fun a x ↦ by
      simpa only [AddMonoidHom.toFun_eq_coe, smul_topNilpotentPoint, RingHom.id_apply] using
        ((ρ.act a).toTopNilpotentPointHom_map φ x).symm
    cont := TopNilpotentPoint.continuous_map φ }

@[simp]
theorem mapTopNilpotentPoint_apply (φ : S →A[R] T) (x : F.TopNilpotentPoint S) :
    ρ.mapTopNilpotentPoint φ x = TopNilpotentPoint.map F φ x := (rfl)

/-- The identity coefficient map acts identically on convergent points. -/
@[simp]
theorem mapTopNilpotentPoint_id :
    letI := ρ.isComm
    letI := ρ.topNilpotentPointModule S
    ρ.mapTopNilpotentPoint (ContinuousAlgHom.id R S) =
      ContinuousLinearMap.id A (F.TopNilpotentPoint S) := by
  let _ := ρ.isComm
  let _ := ρ.topNilpotentPointModule S
  apply ContinuousLinearMap.ext
  intro x
  simp [TopNilpotentPoint.map_id]

/-- Evaluation on convergent points preserves composition of coefficient maps. -/
theorem mapTopNilpotentPoint_comp (ψ : T →A[R] U) (φ : S →A[R] T) :
    letI := ρ.isComm
    letI := ρ.topNilpotentPointModule S
    letI := ρ.topNilpotentPointModule T
    letI := ρ.topNilpotentPointModule U
    ρ.mapTopNilpotentPoint (ψ.comp φ) =
      (ρ.mapTopNilpotentPoint ψ).comp (ρ.mapTopNilpotentPoint φ) := by
  let _ := ρ.isComm
  let _ := ρ.topNilpotentPointModule S
  let _ := ρ.topNilpotentPointModule T
  let _ := ρ.topNilpotentPointModule U
  apply ContinuousLinearMap.ext
  intro x
  simp [TopNilpotentPoint.map_comp]

/-- A continuous algebra map carrying `I` into `J` induces a continuous linear map
between the corresponding point modules. -/
def mapIdealPoint {I : Ideal S} {J : Ideal T} (φ : S →A[R] T) (hφ : Set.MapsTo φ I J) :
    ρ.idealPointSubmodule I →L[A] ρ.idealPointSubmodule J := by
  letI := ρ.isComm
  letI := ρ.topNilpotentPointModule S
  letI := ρ.topNilpotentPointModule T
  apply (ρ.mapTopNilpotentPoint φ).restrict
  intro x hx
  rw [mem_idealPointSubmodule, mapTopNilpotentPoint_apply, TopNilpotentPoint.val_map]
  exact hφ ((ρ.mem_idealPointSubmodule I x).1 hx)

@[simp]
theorem coe_mapIdealPoint {I : Ideal S} {J : Ideal T} (φ : S →A[R] T) (hφ : Set.MapsTo φ I J)
    (x : ρ.idealPointSubmodule I) :
    (ρ.mapIdealPoint φ hφ x : F.TopNilpotentPoint T) = TopNilpotentPoint.map F φ x := (rfl)

/-- The identity algebra map acts as the identity on ideal points. -/
@[simp]
theorem mapIdealPoint_id (I : Ideal S) :
    ρ.mapIdealPoint (ContinuousAlgHom.id R S) (I := I) (J := I) (fun _ hx ↦ hx) =
      ContinuousLinearMap.id A (ρ.idealPointSubmodule I) := by
  generalize_proofs h
  ext x
  simp

/-- Mapping ideal points along a composite agrees with successive coefficient maps. -/
theorem mapIdealPoint_comp {I : Ideal S} {J : Ideal T} {K : Ideal U}
    (ψ : T →A[R] U) (φ : S →A[R] T) (hψ : Set.MapsTo ψ J K) (hφ : Set.MapsTo φ I J) :
    ρ.mapIdealPoint (I := I) (J := K) (ψ.comp φ) (fun _ hx ↦ hψ (hφ hx)) =
      (ρ.mapIdealPoint ψ hψ).comp (ρ.mapIdealPoint φ hφ) := by
  let _ := ρ.isComm
  let _ := ρ.topNilpotentPointModule S
  let _ := ρ.topNilpotentPointModule T
  let _ := ρ.topNilpotentPointModule U
  generalize_proofs h
  unfold mapIdealPoint
  erw [← ContinuousLinearMap.restrict_comp (p₂ := ρ.idealPointSubmodule J)]
  congr 1
  exact ρ.mapTopNilpotentPoint_comp ψ φ

end Coefficients

namespace Hom

variable {ρ} {τ : FormalModule A G}

variable (S) in
/-- A homomorphism of formal modules acts continuously and linearly on convergent points. -/
def toTopNilpotentPointContinuousLinearMap (f : ρ.Hom τ) :
    letI := ρ.isComm
    letI := τ.isComm
    letI := ρ.topNilpotentPointModule S
    letI := τ.topNilpotentPointModule S
    F.TopNilpotentPoint S →L[A] G.TopNilpotentPoint S :=
  letI := ρ.isComm
  letI := τ.isComm
  letI := ρ.topNilpotentPointModule S
  letI := τ.topNilpotentPointModule S
  { f.toFormalGroupHom.toTopNilpotentPointHom S with
    toFun := f.toFormalGroupHom.toTopNilpotentPointHom S
    map_smul' := fun a x ↦ by
      simpa only [FormalGroupHom.toTopNilpotentPointHom_comp, AddMonoidHom.comp_apply,
        smul_topNilpotentPoint, RingHom.id_apply] using
        congrArg (fun g : FormalGroupHom F G ↦ g.toTopNilpotentPointHom S x) (f.comp_act a)
    cont := f.toFormalGroupHom.continuous_toTopNilpotentPointHom }

@[simp]
theorem toTopNilpotentPointContinuousLinearMap_apply (f : ρ.Hom τ) (x : F.TopNilpotentPoint S) :
    f.toTopNilpotentPointContinuousLinearMap S x =
      f.toFormalGroupHom.toTopNilpotentPointHom S x := (rfl)

/-- The identity formal-module homomorphism acts identically on convergent points. -/
@[simp]
theorem toTopNilpotentPointContinuousLinearMap_id (ρ : FormalModule A F) :
    letI := ρ.isComm
    letI := ρ.topNilpotentPointModule S
    (id ρ).toTopNilpotentPointContinuousLinearMap S =
      ContinuousLinearMap.id A (F.TopNilpotentPoint S) := by
  let _ := ρ.isComm
  let _ := ρ.topNilpotentPointModule S
  apply ContinuousLinearMap.ext
  intro x
  simp

/-- Evaluation on convergent points preserves composition of formal-module homomorphisms. -/
theorem toTopNilpotentPointContinuousLinearMap_comp {H : FormalGroup R}
    {υ : FormalModule A H} (g : τ.Hom υ) (f : ρ.Hom τ) :
    letI := ρ.isComm
    letI := τ.isComm
    letI := υ.isComm
    letI := ρ.topNilpotentPointModule S
    letI := τ.topNilpotentPointModule S
    letI := υ.topNilpotentPointModule S
    (g.comp f).toTopNilpotentPointContinuousLinearMap S =
      (g.toTopNilpotentPointContinuousLinearMap S).comp
        (f.toTopNilpotentPointContinuousLinearMap S) := by
  let _ := ρ.isComm
  let _ := τ.isComm
  let _ := υ.isComm
  let _ := ρ.topNilpotentPointModule S
  let _ := τ.topNilpotentPointModule S
  let _ := υ.topNilpotentPointModule S
  apply ContinuousLinearMap.ext
  intro x
  simp [FormalGroupHom.toTopNilpotentPointHom_comp]

/-- A homomorphism of formal modules preserves the point submodule of every ideal. -/
def toIdealPointContinuousLinearMap (f : ρ.Hom τ) (I : Ideal S) :
    ρ.idealPointSubmodule I →L[A] τ.idealPointSubmodule I := by
  letI := ρ.isComm
  letI := τ.isComm
  letI := ρ.topNilpotentPointModule S
  letI := τ.topNilpotentPointModule S
  apply (f.toTopNilpotentPointContinuousLinearMap S).restrict
  intro x hx
  rw [mem_idealPointSubmodule, toTopNilpotentPointContinuousLinearMap_apply]
  exact f.toFormalGroupHom.val_toTopNilpotentPointHom_mem I
    ((ρ.mem_idealPointSubmodule I x).1 hx)

@[simp]
theorem coe_toIdealPointContinuousLinearMap (f : ρ.Hom τ) (I : Ideal S)
    (x : ρ.idealPointSubmodule I) :
    (f.toIdealPointContinuousLinearMap I x : G.TopNilpotentPoint S) =
      f.toFormalGroupHom.toTopNilpotentPointHom S x := (rfl)

/-- The identity formal-module homomorphism acts identically on ideal points. -/
@[simp]
theorem toIdealPointContinuousLinearMap_id (ρ : FormalModule A F) (I : Ideal S) :
    (id ρ).toIdealPointContinuousLinearMap I = ContinuousLinearMap.id A _ := by
  ext x
  simp

/-- Evaluation on ideal points preserves composition of formal-module homomorphisms. -/
theorem toIdealPointContinuousLinearMap_comp {H : FormalGroup R} {υ : FormalModule A H}
    (g : τ.Hom υ) (f : ρ.Hom τ) (I : Ideal S) :
    (g.comp f).toIdealPointContinuousLinearMap I = (g.toIdealPointContinuousLinearMap I).comp
      (f.toIdealPointContinuousLinearMap I) := by
  let _ := ρ.isComm
  let _ := τ.isComm
  let _ := υ.isComm
  let _ := ρ.topNilpotentPointModule S
  let _ := τ.topNilpotentPointModule S
  let _ := υ.topNilpotentPointModule S
  unfold toIdealPointContinuousLinearMap
  erw [← ContinuousLinearMap.restrict_comp (p₂ := τ.idealPointSubmodule I)]
  congr 1
  exact toTopNilpotentPointContinuousLinearMap_comp g f

/-- Applying a formal-module homomorphism to an ideal point commutes with change of
coefficient algebra. -/
theorem toIdealPointContinuousLinearMap_mapIdealPoint {T : Type*} [CommRing T] [Algebra R T]
    [UniformSpace T] [IsUniformAddGroup T] [CompleteSpace T] [T2Space T]
    [IsTopologicalRing T] [IsLinearTopology T T] {I : Ideal S} {J : Ideal T}
    (f : ρ.Hom τ) (φ : S →A[R] T) (hφ : Set.MapsTo φ I J) (x : ρ.idealPointSubmodule I) :
    f.toIdealPointContinuousLinearMap J (ρ.mapIdealPoint φ hφ x) =
      τ.mapIdealPoint φ hφ (f.toIdealPointContinuousLinearMap I x) := by
  apply Subtype.ext
  simp only [coe_toIdealPointContinuousLinearMap, coe_mapIdealPoint]
  exact f.toFormalGroupHom.toTopNilpotentPointHom_map φ x.val

end Hom

/-- A formal-group isomorphism intertwining two formal-module actions induces a continuous
linear equivalence on points in each ideal. -/
def idealPointContinuousLinearEquiv {τ : FormalModule A G} (e : FormalGroupIso F G)
    (he : ∀ a, e.toHom.comp (ρ.act a) = (τ.act a).comp e.toHom) (I : Ideal S) :
    ρ.idealPointSubmodule I ≃L[A] τ.idealPointSubmodule I := by
  let f : ρ.Hom τ := ⟨e.toHom, he⟩
  let E : ρ.idealPointSubmodule I ≃+ τ.idealPointSubmodule I := e.toIdealPointEquiv I
  have hf (x : ρ.idealPointSubmodule I) :
      E x = f.toIdealPointContinuousLinearMap I x :=
    Subtype.ext <| (e.coe_toIdealPointEquiv I x).trans
      (f.coe_toIdealPointContinuousLinearMap I x).symm
  refine
    { E.toLinearEquiv (fun a x ↦ by simp only [hf, map_smul]) with
      continuous_toFun := ?_
      continuous_invFun := ?_ }
  · change Continuous (fun x ↦ E x)
    simpa only [hf] using (f.toIdealPointContinuousLinearMap I).continuous
  · change Continuous (fun x ↦ E.symm x)
    apply continuous_induced_rng.2
    convert e.invHom.continuous_toTopNilpotentPointHom.comp continuous_subtypeVal using 1
    exact funext (e.coe_toIdealPointEquiv_symm I ·)

@[simp]
theorem coe_idealPointContinuousLinearEquiv {τ : FormalModule A G} (e : FormalGroupIso F G)
    (he : ∀ a, e.toHom.comp (ρ.act a) = (τ.act a).comp e.toHom) (I : Ideal S)
    (x : ρ.idealPointSubmodule I) :
    (ρ.idealPointContinuousLinearEquiv e he I x : G.TopNilpotentPoint S) =
      e.toHom.toTopNilpotentPointHom S x :=
  e.coe_toIdealPointEquiv I x

@[simp]
theorem coe_idealPointContinuousLinearEquiv_symm {τ : FormalModule A G} (e : FormalGroupIso F G)
    (he : ∀ a, e.toHom.comp (ρ.act a) = (τ.act a).comp e.toHom) (I : Ideal S)
    (x : τ.idealPointSubmodule I) :
    ((ρ.idealPointContinuousLinearEquiv e he I).symm x : F.TopNilpotentPoint S) =
      e.invHom.toTopNilpotentPointHom S x :=
  e.coe_toIdealPointEquiv_symm I x

/-- The equivalence on ideal points induced by a formal-module isomorphism commutes with
change of coefficient algebra. -/
theorem idealPointContinuousLinearEquiv_mapIdealPoint {τ : FormalModule A G}
    (e : FormalGroupIso F G) (he : ∀ a, e.toHom.comp (ρ.act a) = (τ.act a).comp e.toHom)
    {T : Type*} [CommRing T] [Algebra R T] [UniformSpace T] [IsUniformAddGroup T]
    [CompleteSpace T] [T2Space T] [IsTopologicalRing T] [IsLinearTopology T T]
    {I : Ideal S} {J : Ideal T} (φ : S →A[R] T) (hφ : Set.MapsTo φ I J)
    (x : ρ.idealPointSubmodule I) :
    ρ.idealPointContinuousLinearEquiv e he J (ρ.mapIdealPoint φ hφ x) =
      τ.mapIdealPoint φ hφ (ρ.idealPointContinuousLinearEquiv e he I x) := by
  apply Subtype.ext
  simp only [coe_idealPointContinuousLinearEquiv, coe_mapIdealPoint]
  exact e.toHom.toTopNilpotentPointHom_map φ x.val

/-- Changing formal coordinates induces a continuous linear equivalence on ideal points,
with the transported scalar action on the target. -/
def conjIdealPointContinuousLinearEquiv (e : FormalGroupIso F G) (I : Ideal S) :
    ρ.idealPointSubmodule I ≃L[A] (ρ.conj e).idealPointSubmodule I :=
  ρ.idealPointContinuousLinearEquiv e (ρ.comp_act_conj e) I

@[simp]
theorem coe_conjIdealPointContinuousLinearEquiv (e : FormalGroupIso F G) (I : Ideal S)
    (x : ρ.idealPointSubmodule I) :
    (ρ.conjIdealPointContinuousLinearEquiv e I x : G.TopNilpotentPoint S) =
      e.toHom.toTopNilpotentPointHom S x := by
  simp [conjIdealPointContinuousLinearEquiv]

@[simp]
theorem coe_conjIdealPointContinuousLinearEquiv_symm (e : FormalGroupIso F G) (I : Ideal S)
    (x : (ρ.conj e).idealPointSubmodule I) :
    ((ρ.conjIdealPointContinuousLinearEquiv e I).symm x : F.TopNilpotentPoint S) =
      e.invHom.toTopNilpotentPointHom S x := by
  simp [conjIdealPointContinuousLinearEquiv]

end TauCeti.FormalModule
