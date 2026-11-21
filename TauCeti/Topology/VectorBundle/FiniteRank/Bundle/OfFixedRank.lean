/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.FiberBundle.Pullback
public import TauCeti.Topology.VectorBundle.FiniteRank.Bundle.Basic
public import TauCeti.Topology.VectorBundle.IsEmpty
public import TauCeti.Topology.VectorBundle.Pullback

/-!
# Fixed-rank embedding into variable-rank vector bundles

Constant-rank Mathlib vector bundles `VectorBundle 𝕜 (Fin n → 𝕜) E` embed into
`TauCeti.FiniteRankVectorBundle 𝕜 X` via `FiniteRankVectorBundle.ofFixedRank`, covering `n = 0`
and empty or disconnected bases uniformly, with total-space homeomorphism
`FiniteRankVectorBundle.ofFixedRankTotalSpaceHomeomorph`, trivial bundle specialization
`FiniteRankVectorBundle.trivial`, and essential-image characterization
`FiniteRankVectorBundle.exists_iso_ofFixedRank_iff`.

## References

* A. Hatcher, *Vector Bundles and K-Theory*, §1.1.
* D. Husemoller, *Fibre Bundles*, Chapter 3.
-/

public section

open Bundle CategoryTheory Topology

namespace TauCeti.FiniteRankVectorBundle

universe u v w

variable {X : Type u} [TopologicalSpace X]

section OfFixedRank

variable (𝕜 : Type v) [NontriviallyNormedField 𝕜] (n : ℕ) (E : X → Type w)
  [∀ x, AddCommGroup (E x)] [∀ x, Module 𝕜 (E x)] [∀ x, TopologicalSpace (E x)]
  [TopologicalSpace (TotalSpace (Fin n → 𝕜) E)] [FiberBundle (Fin n → 𝕜) E]
  [VectorBundle 𝕜 (Fin n → 𝕜) E]

/-- View a constant-rank Mathlib `VectorBundle 𝕜 (Fin n → 𝕜) E` as a `FiniteRankVectorBundle 𝕜 X`,
covering `n = 0` and empty or disconnected bases uniformly. -/
-- Expose the rank and fibre projections so `(ofFixedRank 𝕜 n E).Fiber` reduces to `E`.
@[expose, implicit_reducible]
noncomputable def ofFixedRank : FiniteRankVectorBundle.{u, v, w} 𝕜 X :=
  let StratumPkg (k m : ℕ) :=
    let S := {x : X // LocallyConstant.const X n x = m}
    Σ' (ts : TopologicalSpace (TotalSpace (Fin k → 𝕜) (fun y : S ↦ E y.val))),
      Σ' (fb : @FiberBundle S (Fin k → 𝕜) _ _ (fun y ↦ E y.val) ts _),
        @VectorBundle 𝕜 S (Fin k → 𝕜) (fun y ↦ E y.val) _ (fun _ ↦ inferInstance)
          (fun _ ↦ inferInstance) inferInstance inferInstance _ ts _ fb
  let data (m : ℕ) : StratumPkg m m :=
    let S := {x : X // LocallyConstant.const X n x = m}
    if h : n = m then
      h.rec (motive := fun k _ ↦ StratumPkg k m)
        (let inc : C(S, X) := ⟨Subtype.val, continuous_subtypeVal⟩
        ⟨Pullback.TotalSpace.topologicalSpace (Fin n → 𝕜) E ⇑inc,
         FiberBundle.pullback (F := Fin n → 𝕜) (E := E) inc,
         VectorBundle.pullback (𝕜 := 𝕜) (F := Fin n → 𝕜) (E := E) inc⟩)
    else
      have hEmpty : IsEmpty S := ⟨fun y ↦ h y.property⟩
      ⟨⊥, @fiberBundleOfIsEmpty S _ hEmpty (Fin m → 𝕜) (fun y : S ↦ E y.val) ⊥ _ _,
       @vectorBundleOfIsEmpty S _ hEmpty (Fin m → 𝕜) (fun y : S ↦ E y.val) ⊥ _ 𝕜 _ _ _ _ _⟩
  { rank := LocallyConstant.const X n, Fiber := E
    topologicalSpaceStratumTotalSpace m := (data m).fst
    fiberBundleStratum m := (data m).snd.fst, vectorBundleStratum m := (data m).snd.snd }

@[simp] theorem rank_ofFixedRank : (ofFixedRank 𝕜 n E).rank = LocallyConstant.const X n := by rfl
@[simp] theorem fiber_ofFixedRank : (ofFixedRank 𝕜 n E).Fiber = E := by rfl
@[simp] theorem topologicalSpaceStratumTotalSpace_ofFixedRank_self :
    (ofFixedRank 𝕜 n E).topologicalSpaceStratumTotalSpace n =
      Pullback.TotalSpace.topologicalSpace (Fin n → 𝕜) E
        (Subtype.val : {x : X // LocallyConstant.const X n x = n} → X) :=
  congrArg PSigma.fst (dite_eq_left_of_eq_true (eq_true rfl))

private noncomputable def stratumTotalSpaceOfFixedRankSelfPkg :
    { e : TotalSpace (Fin n → 𝕜) ((ofFixedRank 𝕜 n E).StratumFiber n) ≃ₜ TotalSpace (Fin n → 𝕜) E //
      (∀ q, e q = ⟨q.proj.val, q.snd⟩) ∧ (∀ r, e.symm r = ⟨⟨r.proj, rfl⟩, r.snd⟩) } :=
  let S := {x : X // LocallyConstant.const X n x = n}
  let val : S → X := Subtype.val
  let aux : ∀ (t : TopologicalSpace (TotalSpace (Fin n → 𝕜) (fun y : S ↦ E y.val))),
      t = Pullback.TotalSpace.topologicalSpace (Fin n → 𝕜) E val →
      { e : @Homeomorph (TotalSpace (Fin n → 𝕜) (fun y : S ↦ E y.val))
          (TotalSpace (Fin n → 𝕜) E) t inferInstance //
        (∀ q, e q = ⟨q.proj.val, q.snd⟩) ∧ (∀ r, e.symm r = ⟨⟨r.proj, rfl⟩, r.snd⟩) } := by
    rintro _ rfl
    letI : TopologicalSpace (TotalSpace (Fin n → 𝕜) (fun y : S ↦ E y.val)) :=
      Pullback.TotalSpace.topologicalSpace (Fin n → 𝕜) E val
    let hproj := FiberBundle.continuous_proj (Fin n → 𝕜) E
    refine ⟨{ toFun q := ⟨q.proj.val, q.snd⟩, invFun r := ⟨⟨r.proj, rfl⟩, r.snd⟩
              left_inv := fun ⟨⟨_, _⟩, _⟩ ↦ rfl, right_inv := fun ⟨_, _⟩ ↦ rfl
              continuous_toFun := Pullback.continuous_lift (Fin n → 𝕜) E val
              continuous_invFun := ?_ }, fun _ ↦ rfl, fun _ ↦ rfl⟩
    let inc : X → S := fun b ↦ ⟨b, rfl⟩
    exact ((Pullback.continuous_lift (Fin n → 𝕜) (val *ᵖ E) inc).comp
      (Bundle.Pullback.subtypeHomeomorph (Fin n → 𝕜) E (fun _ ↦ rfl) hproj).symm.continuous).congr
        fun r ↦ congrArg (Pullback.lift inc)
          (Bundle.Pullback.subtypeHomeomorph_symm_apply (Fin n → 𝕜) E (fun _ ↦ rfl) hproj r)
  aux ((ofFixedRank 𝕜 n E).topologicalSpaceStratumTotalSpace n)
    (topologicalSpaceStratumTotalSpace_ofFixedRank_self 𝕜 n E)

/-- The glued total space of `ofFixedRank 𝕜 n E` is homeomorphic over `X` to the native Mathlib
`TotalSpace (Fin n → 𝕜) E`. -/
noncomputable def ofFixedRankTotalSpaceHomeomorph :
    TotalSpace Unit (ofFixedRank 𝕜 n E).Fiber ≃ₜ TotalSpace (Fin n → 𝕜) E :=
  let pkg := stratumTotalSpaceOfFixedRankSelfPkg 𝕜 n E
  VariableRankBundle.totalSpaceHomeomorphOfConstStratum (ofFixedRank 𝕜 n E) (fun _ ↦ rfl) pkg.val
    (fun _ ↦ Equiv.refl _) (fun x v ↦ pkg.property.1 ⟨⟨x, rfl⟩, v⟩)
    (fun x v ↦ pkg.property.2 ⟨x, v⟩)

@[simp] theorem ofFixedRankTotalSpaceHomeomorph_apply
    (p : TotalSpace Unit (ofFixedRank 𝕜 n E).Fiber) :
    ofFixedRankTotalSpaceHomeomorph 𝕜 n E p = ⟨p.proj, p.snd⟩ :=
  VariableRankBundle.totalSpaceHomeomorphOfConstStratum_apply _ _ _ _ _ _ p

@[simp] theorem ofFixedRankTotalSpaceHomeomorph_symm_apply (p : TotalSpace (Fin n → 𝕜) E) :
    (ofFixedRankTotalSpaceHomeomorph 𝕜 n E).symm p = ⟨p.proj, p.snd⟩ :=
  VariableRankBundle.totalSpaceHomeomorphOfConstStratum_symm_apply _ _ _ _ _ _ p

end OfFixedRank

/-- The trivial variable-rank vector bundle `X × (Fin n → 𝕜)` of constant rank `n`. -/
noncomputable abbrev trivial (𝕜 : Type v) [NontriviallyNormedField 𝕜]
    (X : Type u) [TopologicalSpace X] (n : ℕ) : FiniteRankVectorBundle.{u, v, v} 𝕜 X :=
  ofFixedRank 𝕜 n (Bundle.Trivial X (Fin n → 𝕜))

/-- A variable-rank vector bundle is isomorphic to `ofFixedRank 𝕜 n E` for some constant-rank
Mathlib `VectorBundle 𝕜 (Fin n → 𝕜) E` over `X` if and only if its rank function is constantly
`n`. -/
theorem exists_iso_ofFixedRank_iff {𝕜 : Type v} [NontriviallyNormedField 𝕜]
    {X : Type u} [TopologicalSpace X] (V : FiniteRankVectorBundle.{u, v, w} 𝕜 X) (n : ℕ) :
    (∃ (E : X → Type w) (_ : ∀ x, AddCommGroup (E x)) (_ : ∀ x, Module 𝕜 (E x))
        (_ : ∀ x, TopologicalSpace (E x)) (_ : TopologicalSpace (TotalSpace (Fin n → 𝕜) E))
        (_ : FiberBundle (Fin n → 𝕜) E) (_ : VectorBundle 𝕜 (Fin n → 𝕜) E),
      Nonempty (ofFixedRank 𝕜 n E ≅ V)) ↔ V.rank = LocallyConstant.const X n := by
  refine ⟨fun ⟨_, _, _, _, _, _, _, ⟨e⟩⟩ ↦ e.symm.variableRankBundle_rank_eq, fun hn ↦ ?_⟩
  have hnx (x : X) : VariableRankBundle.rank V x = n := congrFun (congrArg DFunLike.coe hn) x
  let inc := VariableRankBundle.constRankInclusion (V := V) hnx
  refine ⟨(⇑inc) *ᵖ (V.StratumFiber n),
    inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    ⟨VariableRankBundle.isoOfTotalSpaceHomeomorph (fun x ↦ LinearEquiv.refl 𝕜 (V.Fiber x))
      ((ofFixedRankTotalSpaceHomeomorph 𝕜 n ((⇑inc) *ᵖ (V.StratumFiber n))).trans
        (VariableRankBundle.constRankTotalSpaceHomeomorph V hnx).symm) fun x v ↦ by
        rw [Homeomorph.trans_apply, ofFixedRankTotalSpaceHomeomorph_apply,
          VariableRankBundle.constRankTotalSpaceHomeomorph_symm_apply]
        exact TotalSpace.ext rfl
          (heq_of_eq (FiniteRankVectorBundle.stratumFiberEquiv_apply V ⟨x, hnx x⟩ v))⟩⟩

end TauCeti.FiniteRankVectorBundle
