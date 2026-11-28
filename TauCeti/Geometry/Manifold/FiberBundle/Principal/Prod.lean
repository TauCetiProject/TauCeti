/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.FiberBundle.Basic
public import TauCeti.Topology.FiberBundle.Principal.Prod
import TauCeti.Topology.FiberBundle.Prod

/-!
# Smooth fibrewise products of principal bundles

The fibrewise product of two `C^n` principal bundles over the same base is a `C^n` principal
bundle for the product group (`TauCeti.PrincipalBundle.FiberProd.instContMDiffFiberBundle`).
The bundle atlas is Mathlib's `FiberBundle.prod`, and the componentwise action is supplied by
`TauCeti.PrincipalBundle.FiberProd.instPrincipalBundle`.

The projections detect smoothness of maps into the charted total space
(`TauCeti.PrincipalBundle.FiberProd.contMDiff_iff`), using the preferred-chart criterion
`TauCeti.ManifoldTotalSpace.contMDiffWithinAt_iff`. Pairs with equal base projections lift
uniquely to a smooth map (`TauCeti.PrincipalBundle.FiberProd.existsUnique_contMDiff_of_proj_eq`).

## References

* D. Husemoller, *Fibre Bundles*, 3rd ed., Springer, 1994, Chapter 4, §4
  (fibre products of principal bundles).
-/

public section

open Bundle Set
open scoped Manifold ContDiff

namespace TauCeti.PrincipalBundle.FiberProd

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {n : ℕ∞ω}
  {B G H : Type*} [TopologicalSpace B] [TopologicalSpace G] [TopologicalSpace H]
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB] {HB : Type*} [TopologicalSpace HB]
  {IB : ModelWithCorners 𝕜 EB HB} [ChartedSpace HB B]
  {EG : Type*} [NormedAddCommGroup EG] [NormedSpace 𝕜 EG] {HG : Type*} [TopologicalSpace HG]
  {IG : ModelWithCorners 𝕜 EG HG} [ChartedSpace HG G]
  {EH : Type*} [NormedAddCommGroup EH] [NormedSpace 𝕜 EH] {HH : Type*} [TopologicalSpace HH]
  {IH : ModelWithCorners 𝕜 EH HH} [ChartedSpace HH H]
  {P Q : B → Type*} [TopologicalSpace (TotalSpace G P)] [∀ b, TopologicalSpace (P b)]
  [TopologicalSpace (TotalSpace H Q)] [∀ b, TopologicalSpace (Q b)]
  [FiberBundle G P] [FiberBundle H Q] [One G] [One H]

/-- The fibrewise product of two `C^n` fibre bundles is `C^n`: its changes of fibre
coordinates are products of the changes in the factors. The model fibres have distinguished
points `1` as required by `FiberProd.instFiberBundle`. This applies in particular to principal
bundles with the componentwise action (Husemoller, Chapter 4, §4). -/
instance instContMDiffFiberBundle
    [ContMDiffFiberBundle n G P IB IG] [ContMDiffFiberBundle n H Q IB IH] :
    ContMDiffFiberBundle n (G × H) (FiberProd P Q) IB (IG.prod IH) where
  contMDiffOn_coordChange e e' he he' := by
    obtain ⟨eG, eH, hG, hH, rfl⟩ := he.out
    obtain ⟨eG', eH', hG', hH', rfl⟩ := he'.out
    let overlap : Set (B × G × H) :=
      ((eG.baseSet ∩ eH.baseSet) ∩ (eG'.baseSet ∩ eH'.baseSet)) ×ˢ univ
    have hg : ContMDiffOn (IB.prod (IG.prod IH)) IG n
        (fun p : B × G × H ↦ eG.coordChange eG' p.1 p.2.1) overlap := by
      exact (ContMDiffFiberBundle.contMDiffOn_coordChange eG eG').comp
        (contMDiffOn_fst.prodMk (contMDiff_fst.comp_contMDiffOn contMDiffOn_snd))
        (fun _ hx ↦ ⟨⟨hx.1.1.1, hx.1.2.1⟩, mem_univ _⟩)
    have hh : ContMDiffOn (IB.prod (IG.prod IH)) IH n
        (fun p : B × G × H ↦ eH.coordChange eH' p.1 p.2.2) overlap := by
      exact (ContMDiffFiberBundle.contMDiffOn_coordChange eH eH').comp
        (contMDiffOn_fst.prodMk (contMDiff_snd.comp_contMDiffOn contMDiffOn_snd))
        (fun _ hx ↦ ⟨⟨hx.1.1.2, hx.1.2.2⟩, mem_univ _⟩)
    refine (hg.prodMk hh).congr ?_
    rintro ⟨b, g, h⟩ hb
    -- These are the same distinguished fibre points that `instFiberBundle` uses for
    -- the inverse trivialization outside its base set.
    let : ∀ b, Zero (P b) := fun b ↦ ⟨(FiberBundle.homeomorphAt G P b).symm 1⟩
    let : ∀ b, Zero (Q b) := fun b ↦ ⟨(FiberBundle.homeomorphAt H Q b).symm 1⟩
    exact eG.coordChange_prod eG' eH eH' hb.1.1.1 hb.1.1.2 g h

variable {M EM HM : Type*} [TopologicalSpace M]
  [NormedAddCommGroup EM] [NormedSpace 𝕜 EM] [TopologicalSpace HM]
  {IM : ModelWithCorners 𝕜 EM HM} [ChartedSpace HM M]
  {f : M → TotalSpace (G × H) (FiberProd P Q)}

/-- A family in a fibrewise product is `C^n` within a set at a point if and only if both
component families are `C^n` there. This does not require smooth transition functions. -/
theorem contMDiffWithinAt_iff {s : Set M} {x : M} :
    ContMDiffWithinAt IM (IB.prod (IG.prod IH)) n
      (fun y ↦ ManifoldTotalSpace.homeomorph (G × H) (FiberProd P Q) (f y)) s x ↔
      ContMDiffWithinAt IM (IB.prod IG) n
        (fun y ↦ ManifoldTotalSpace.homeomorph G P ⟨(f y).proj, (f y).snd.fst⟩) s x ∧
      ContMDiffWithinAt IM (IB.prod IH) n
        (fun y ↦ ManifoldTotalSpace.homeomorph H Q ⟨(f y).proj, (f y).snd.snd⟩) s x := by
  rw [ManifoldTotalSpace.contMDiffWithinAt_iff, ManifoldTotalSpace.contMDiffWithinAt_iff,
    ManifoldTotalSpace.contMDiffWithinAt_iff]
  simp only [trivializationAt_snd, contMDiffWithinAt_prod_iff, Function.comp_def]
  tauto

/-- A map into the charted total space of a fibrewise product is `C^n` if and only if both
of its projections are `C^n`. In particular, a pair of smooth maps into the two factors
with a common base projection has a smooth lift to the fibrewise product. -/
theorem contMDiff_iff :
    ContMDiff IM (IB.prod (IG.prod IH)) n
      (fun y ↦ ManifoldTotalSpace.homeomorph (G × H) (FiberProd P Q) (f y)) ↔
      ContMDiff IM (IB.prod IG) n
        (fun y ↦ ManifoldTotalSpace.homeomorph G P ⟨(f y).proj, (f y).snd.fst⟩) ∧
      ContMDiff IM (IB.prod IH) n
        (fun y ↦ ManifoldTotalSpace.homeomorph H Q ⟨(f y).proj, (f y).snd.snd⟩) := by
  simp only [ContMDiff, ← contMDiffWithinAt_univ, contMDiffWithinAt_iff, forall_and]

/-- Two `C^n` families with the same base projection lift uniquely to a `C^n` family
in the fibrewise product. -/
theorem existsUnique_contMDiff_of_proj_eq {p : M → TotalSpace G P} {q : M → TotalSpace H Q}
    (hp : ContMDiff IM (IB.prod IG) n (fun x ↦ ManifoldTotalSpace.homeomorph G P (p x)))
    (hq : ContMDiff IM (IB.prod IH) n (fun x ↦ ManifoldTotalSpace.homeomorph H Q (q x)))
    (hproj : ∀ x, (p x).proj = (q x).proj) :
    ∃! f : M → TotalSpace (G × H) (FiberProd P Q),
      ContMDiff IM (IB.prod (IG.prod IH)) n
        (fun x ↦ ManifoldTotalSpace.homeomorph (G × H) (FiberProd P Q) (f x)) ∧
      ∀ x, ((⟨(f x).proj, (f x).snd.fst⟩ : TotalSpace G P),
        (⟨(f x).proj, (f x).snd.snd⟩ : TotalSpace H Q)) = (p x, q x) := by
  let diag (z : TotalSpace (G × H) (FiberProd P Q)) : TotalSpace G P × TotalSpace H Q :=
    (⟨z.proj, z.snd.fst⟩, ⟨z.proj, z.snd.snd⟩)
  let lift (x : M) : TotalSpace (G × H) (FiberProd P Q) :=
    ⟨(p x).proj, mk (p x).snd (cast (congrArg Q (hproj x).symm) (q x).snd)⟩
  have hlift (x : M) : diag (lift x) = (p x, q x) := by
    simp only [diag, lift, fst_mk, snd_mk, TotalSpace.mk_cast (hproj x).symm, TotalSpace.eta]
  have hsmooth : ContMDiff IM (IB.prod (IG.prod IH)) n
      (fun x ↦ ManifoldTotalSpace.homeomorph (G × H) (FiberProd P Q) (lift x)) := by
    refine contMDiff_iff.2 ⟨hp.congr ?_, hq.congr ?_⟩
    · exact fun x ↦ congrArg (ManifoldTotalSpace.homeomorph G P) (congrArg Prod.fst (hlift x))
    · exact fun x ↦ congrArg (ManifoldTotalSpace.homeomorph H Q) (congrArg Prod.snd (hlift x))
  refine ⟨lift, ⟨hsmooth, hlift⟩, fun g hg ↦ ?_⟩
  have hinj : Function.Injective diag := by
    rintro ⟨b, z⟩ ⟨b', z'⟩ heq
    have hbase : b = b' := congrArg (fun v : TotalSpace G P × TotalSpace H Q ↦ v.1.proj) heq
    subst b'
    simp only [diag, Prod.mk.injEq, TotalSpace.mk_inj] at heq
    exact congrArg (TotalSpace.mk b) (FiberProd.ext heq.1 heq.2)
  exact funext fun x ↦ hinj ((hg.2 x).trans (hlift x).symm)

end TauCeti.PrincipalBundle.FiberProd
