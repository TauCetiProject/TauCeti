/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Homotopy.ConnectedMap
public import TauCeti.Topology.Homotopy.SerreFibration.Connected

/-!
# Homology of the fibre inclusion over a highly connected base

Let `p : E → B` be a Serre fibration and `b : B` a point at which `π_k(B, b)` is trivial for every
`k ≤ n`, so that `B` is path-connected and `n`-connected. The inclusion of the fibre
`F = p⁻¹(b) → E` is then an `n`-connected map
(`TauCeti.TopCat.isNConnected_fiberι_of_mem_serreFibrations`), so it induces isomorphisms
`H_m(F; R) → H_m(E; R)` for `m < n` and surjections for `m = n`, with coefficients in any ring
`R`.

This is the comparison between the homology of a fibre and of the total space that is usually read
off the Serre spectral sequence, whose `E²` page vanishes in the columns `1 ≤ p ≤ n`; here it
follows from the exact homotopy sequence and the homology comparison for `n`-connected maps.
Barraud, Damian, Humilière and Oancea apply it to the evaluation fibration
`P_{Q→Y} 𝓛₀ Q → Y` with fibre `Ω²Q` over a highly connected submanifold `Y` (Lemma 7.7), and to
double loop spaces of sphere bundles over highly connected bases (Proposition 6.23).

Pulling `p` back along a path `γ` in `B` to the contractible interval `ULift unitInterval` makes the
endpoint fibre inclusions weak homotopy equivalences, giving path transport isomorphisms
`H_n(p⁻¹(b₀); M) ≅ H_n(p⁻¹(b₁); M)` with coefficients in any `R`-module `M`
(`TauCeti.TopCat.fiberSingularHomologyIsoOfPath`), compatible with the fibre inclusions into `E`
and functorial with respect to path homotopy, reversal, and concatenation.

## Main results

* `TauCeti.TopCat.isIso_singularHomologyMap_fiberι`: the fibre inclusion is an isomorphism on
  `H_m` for `m < n`.
* `TauCeti.TopCat.epi_singularHomologyMap_fiberι`: the fibre inclusion is surjective on `H_n`.
* `TauCeti.TopCat.fiberSingularHomologyIsoOfPath`: a path in `B` induces singular homology
  isomorphisms between the fibres over its endpoints in every degree and for any coefficient module
  `M`, compatible with `p.fiberι` (`fiberSingularHomologyIsoOfPath_hom_comp_map_fiberι`), constant
  paths (`fiberSingularHomologyIsoOfPath_refl`), path reversal
  (`fiberSingularHomologyIsoOfPath_symm`), concatenation (`fiberSingularHomologyIsoOfPath_trans`),
  and homotopy (`fiberSingularHomologyIsoOfPath_congr`).

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Theorem 4.41 and Proposition 4.21.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, Proposition 6.23 and Lemma 7.7.
-/

public section

open CategoryTheory AlgebraicTopology
open scoped Topology Topology.Homotopy

universe u v

namespace TauCeti.TopCat

section ConnectedBase

variable {E B : TopCat.{u}} {p : E ⟶ B} {b : B} {n : ℕ} (R : Type u) [Ring R]

/-- **The fibre inclusion over an `n`-connected base is a homology isomorphism below degree `n`.**
For a Serre fibration `p : E → B` and a point `b` with `π_k(B, b)` trivial for every `k ≤ n`, the
inclusion of the fibre `p⁻¹(b) → E` induces isomorphisms `H_m(p⁻¹(b); R) → H_m(E; R)` for every
`m < n`. -/
theorem isIso_singularHomologyMap_fiberι (hp : serreFibrations p)
    (hB : ∀ k ≤ n, Subsingleton (π_ k B b)) {m : ℕ} (hm : m < n) :
    IsIso (((singularHomologyFunctor (ModuleCat.{u} R) m).obj (ModuleCat.of R R)).map
      (p.fiberι b)) :=
  (isNConnected_fiberι_of_mem_serreFibrations hp hB).isIso_singularHomologyMap R hm

/-- **The fibre inclusion over an `n`-connected base is surjective on homology in degree `n`.**
For a Serre fibration `p : E → B` and a point `b` with `π_k(B, b)` trivial for every `k ≤ n`, the
inclusion of the fibre `p⁻¹(b) → E` induces surjections `H_m(p⁻¹(b); R) → H_m(E; R)` for every
`m ≤ n`. -/
theorem epi_singularHomologyMap_fiberι (hp : serreFibrations p)
    (hB : ∀ k ≤ n, Subsingleton (π_ k B b)) {m : ℕ} (hm : m ≤ n) :
    Epi (((singularHomologyFunctor (ModuleCat.{u} R) m).obj (ModuleCat.of R R)).map
      (p.fiberι b)) :=
  (isNConnected_fiberι_of_mem_serreFibrations hp hB).epi_singularHomologyMap R hm

end ConnectedBase

section PathTransport

private instance contractibleSpace_ulift_unitInterval :
    ContractibleSpace (_root_.TopCat.of (ULift.{u} unitInterval)) :=
  have : ContractibleSpace unitInterval :=
    (convex_Icc (0 : ℝ) 1).contractibleSpace ⟨0, unitInterval.zero_mem⟩
  Homeomorph.ulift.contractibleSpace

private instance contractibleSpace_ulift_unitInterval_prod :
    ContractibleSpace (_root_.TopCat.of (ULift.{u} (unitInterval × unitInterval))) :=
  have : ContractibleSpace unitInterval :=
    (convex_Icc (0 : ℝ) 1).contractibleSpace ⟨0, unitInterval.zero_mem⟩
  Homeomorph.ulift.contractibleSpace

/-- Over a contractible base, the inclusion of any fibre of a Serre fibration is a weak homotopy
equivalence, and hence induces an isomorphism on singular homology with arbitrary module
coefficients. -/
private lemma isIso_singularHomologyMap_fiberι_of_contractibleSpace
    {E B : _root_.TopCat.{u}} {p : E ⟶ B} (hp : serreFibrations p) [ContractibleSpace B]
    {R : Type v} [Ring R] (M : ModuleCat.{u} R) (b : B) (n : ℕ) :
    IsIso (((singularHomologyFunctor (ModuleCat.{u} R) n).obj M).map (p.fiberι b)) := by
  have hw : (p.fiberι b).hom.IsWeakHomotopyEquivalence :=
    ContinuousMap.isWeakHomotopyEquivalence_iff_forall_isNConnected.2 fun _ ↦
      isNConnected_fiberι_of_mem_serreFibrations hp fun _ _ ↦ inferInstance
  exact hw.isIso_singularHomologyMap M n

private lemma eqToHom_fiber_comp_fiberι {E B : _root_.TopCat.{u}} (p : E ⟶ B)
    {b b' : B} (h : b = b') :
    eqToHom (congrArg p.fiber h) ≫ p.fiberι b' = p.fiberι b := by
  subst h
  exact Category.id_comp _

/-- **Path transport on singular homology of fibres of a Serre fibration.** A path `γ` from `b₀` to
`b₁` in `B` induces an isomorphism `H_n(p⁻¹(b₀); M) ≅ H_n(p⁻¹(b₁); M)` in every degree `n` for any
coefficient module `M`, obtained by pulling `p` back to the contractible interval
`ULift unitInterval` and inverting the homology maps of the endpoint fibre inclusions. -/
noncomputable def fiberSingularHomologyIsoOfPath {E B : _root_.TopCat.{u}} {p : E ⟶ B}
    (hp : serreFibrations p) {R : Type v} [Ring R] (M : ModuleCat.{u} R)
    {b₀ b₁ : B} (γ : Path b₀ b₁) (n : ℕ) :
    (((singularHomologyFunctor (ModuleCat.{u} R) n).obj M).obj (p.fiber b₀)) ≅
      (((singularHomologyFunctor (ModuleCat.{u} R) n).obj M).obj (p.fiber b₁)) :=
  let F := (singularHomologyFunctor (ModuleCat.{u} R) n).obj M
  let g : _root_.TopCat.of (ULift.{u} unitInterval) ⟶ B :=
    _root_.TopCat.ofHom ⟨fun t ↦ γ t.down, γ.continuous.comp continuous_uliftDown⟩
  let p' := _root_.TopCat.pullbackFst g p
  have hp' : serreFibrations p' := mem_serreFibrations_pullbackFst hp g
  have : IsIso (F.map (p'.fiberι (ULift.up (0 : unitInterval)))) :=
    isIso_singularHomologyMap_fiberι_of_contractibleSpace hp' M _ n
  have : IsIso (F.map (p'.fiberι (ULift.up (1 : unitInterval)))) :=
    isIso_singularHomologyMap_fiberι_of_contractibleSpace hp' M _ n
  F.mapIso (eqToIso (congrArg p.fiber γ.source.symm) ≪≫
      (p.fiberPullbackFstIso g (ULift.up (0 : unitInterval))).symm) ≪≫
    asIso (F.map (p'.fiberι (ULift.up (0 : unitInterval)))) ≪≫
    (asIso (F.map (p'.fiberι (ULift.up (1 : unitInterval))))).symm ≪≫
    F.mapIso (p.fiberPullbackFstIso g (ULift.up (1 : unitInterval)) ≪≫
      eqToIso (congrArg p.fiber γ.target))

variable {E B : _root_.TopCat.{u}} {p : E ⟶ B} (hp : serreFibrations p)
  {R : Type v} [Ring R] (M : ModuleCat.{u} R)

/-- Path transport along `γ : Path b₀ b₁` commutes with the homology maps induced by the fibre
inclusions `p⁻¹(b₀) ⟶ E` and `p⁻¹(b₁) ⟶ E`. -/
@[reassoc (attr := simp)]
theorem fiberSingularHomologyIsoOfPath_hom_comp_map_fiberι {b₀ b₁ : B} (γ : Path b₀ b₁) (n : ℕ) :
    (fiberSingularHomologyIsoOfPath hp M γ n).hom ≫
        ((singularHomologyFunctor (ModuleCat.{u} R) n).obj M).map (p.fiberι b₁) =
      ((singularHomologyFunctor (ModuleCat.{u} R) n).obj M).map (p.fiberι b₀) := by
  let F := (singularHomologyFunctor (ModuleCat.{u} R) n).obj M
  let g : _root_.TopCat.of (ULift.{u} unitInterval) ⟶ B :=
    _root_.TopCat.ofHom ⟨fun t ↦ γ t.down, γ.continuous.comp continuous_uliftDown⟩
  let p' := _root_.TopCat.pullbackFst g p
  have hp' : serreFibrations p' := mem_serreFibrations_pullbackFst hp g
  let t₀ : _root_.TopCat.of (ULift.{u} unitInterval) := ULift.up (0 : unitInterval)
  let t₁ : _root_.TopCat.of (ULift.{u} unitInterval) := ULift.up (1 : unitInterval)
  have : IsIso (F.map (p'.fiberι t₀)) :=
    isIso_singularHomologyMap_fiberι_of_contractibleSpace hp' M t₀ n
  have : IsIso (F.map (p'.fiberι t₁)) :=
    isIso_singularHomologyMap_fiberι_of_contractibleSpace hp' M t₁ n
  have ht₁_top : (p.fiberPullbackFstIso g t₁ ≪≫ eqToIso (congrArg p.fiber γ.target)).hom ≫
      p.fiberι b₁ = p'.fiberι t₁ ≫ _root_.TopCat.pullbackSnd g p := by
    rw [Iso.trans_hom, eqToIso.hom, Category.assoc, eqToHom_fiber_comp_fiberι p γ.target]
    exact p.fiberPullbackFstIso_hom_comp_fiberι g t₁
  have ht₀_top : (eqToIso (congrArg p.fiber γ.source.symm) ≪≫
        (p.fiberPullbackFstIso g t₀).symm).hom ≫
      p'.fiberι t₀ ≫ _root_.TopCat.pullbackSnd g p = p.fiberι b₀ := by
    rw [← p.fiberPullbackFstIso_hom_comp_fiberι g t₀, Iso.trans_hom, Iso.symm_hom,
      eqToIso.hom, Category.assoc, Iso.inv_hom_id_assoc]
    exact eqToHom_fiber_comp_fiberι p γ.source.symm
  have ht₁ : F.map (p.fiberPullbackFstIso g t₁ ≪≫ eqToIso (congrArg p.fiber γ.target)).hom ≫
      F.map (p.fiberι b₁) = F.map (p'.fiberι t₁) ≫ F.map (_root_.TopCat.pullbackSnd g p) := by
    simpa only [F.map_comp] using congrArg F.map ht₁_top
  have ht₀ : F.map (eqToIso (congrArg p.fiber γ.source.symm) ≪≫
        (p.fiberPullbackFstIso g t₀).symm).hom ≫
      F.map (p'.fiberι t₀) ≫ F.map (_root_.TopCat.pullbackSnd g p) = F.map (p.fiberι b₀) := by
    simpa only [F.map_comp, Category.assoc] using congrArg F.map ht₀_top
  change (F.map (eqToIso (congrArg p.fiber γ.source.symm) ≪≫
        (p.fiberPullbackFstIso g t₀).symm).hom ≫
      F.map (p'.fiberι t₀) ≫ (asIso (F.map (p'.fiberι t₁))).inv ≫
      F.map (p.fiberPullbackFstIso g t₁ ≪≫ eqToIso (congrArg p.fiber γ.target)).hom) ≫
    F.map (p.fiberι b₁) = F.map (p.fiberι b₀)
  simp only [Category.assoc, asIso_inv]
  rw [ht₁, IsIso.inv_hom_id_assoc]
  exact ht₀

/-- The inverse of `fiberSingularHomologyIsoOfPath` commutes with the homology maps induced by the
fibre inclusions `p⁻¹(b₁) ⟶ E` and `p⁻¹(b₀) ⟶ E`. -/
@[reassoc (attr := simp)]
theorem fiberSingularHomologyIsoOfPath_inv_comp_map_fiberι {b₀ b₁ : B} (γ : Path b₀ b₁) (n : ℕ) :
    (fiberSingularHomologyIsoOfPath hp M γ n).inv ≫
        ((singularHomologyFunctor (ModuleCat.{u} R) n).obj M).map (p.fiberι b₀) =
      ((singularHomologyFunctor (ModuleCat.{u} R) n).obj M).map (p.fiberι b₁) :=
  (Iso.inv_comp_eq _).2 (fiberSingularHomologyIsoOfPath_hom_comp_map_fiberι hp M γ n).symm

/-- Over a contractible base, path transport along any path `γ : Path b₀ b₁` is simply
`F.map (p.fiberι b₀)` followed by `(F.map (p.fiberι b₁))⁻¹`, and in particular depends only on the
endpoints `b₀` and `b₁`. -/
private lemma fiberSingularHomologyIsoOfPath_eq_of_contractibleSpace [ContractibleSpace B]
    {b₀ b₁ : B} (γ : Path b₀ b₁) (n : ℕ) :
    have := isIso_singularHomologyMap_fiberι_of_contractibleSpace hp M b₀ n
    have := isIso_singularHomologyMap_fiberι_of_contractibleSpace hp M b₁ n
    fiberSingularHomologyIsoOfPath hp M γ n =
      asIso (((singularHomologyFunctor (ModuleCat.{u} R) n).obj M).map (p.fiberι b₀)) ≪≫
        (asIso (((singularHomologyFunctor (ModuleCat.{u} R) n).obj M).map (p.fiberι b₁))).symm := by
  have := isIso_singularHomologyMap_fiberι_of_contractibleSpace hp M b₀ n
  have := isIso_singularHomologyMap_fiberι_of_contractibleSpace hp M b₁ n
  apply Iso.ext
  refine (cancel_mono (((singularHomologyFunctor (ModuleCat.{u} R) n).obj M).map
    (p.fiberι b₁))).1 ?_
  rw [fiberSingularHomologyIsoOfPath_hom_comp_map_fiberι]
  simp

/-- Base change compatibility of `fiberSingularHomologyIsoOfPath` along a morphism `f : B' ⟶ B`:
if `γ'` is a path in `B'` lifting `γ` in `B` along `f`, then path transport along `γ` is conjugate
via `p.fiberPullbackFstIso f` to path transport along `γ'` for `TopCat.pullbackFst f p`. -/
private lemma fiberSingularHomologyIsoOfPath_pullbackFst {B' : _root_.TopCat.{u}} (f : B' ⟶ B)
    {x₀ x₁ : B'} (γ' : Path x₀ x₁) {b₀ b₁ : B} (γ : Path b₀ b₁)
    (hb₀ : f x₀ = b₀) (hb₁ : f x₁ = b₁) (hγ : ∀ t, f (γ' t) = γ t) (n : ℕ) :
    let F := (singularHomologyFunctor (ModuleCat.{u} R) n).obj M
    fiberSingularHomologyIsoOfPath hp M γ n =
      F.mapIso (eqToIso (congrArg p.fiber hb₀.symm) ≪≫ (p.fiberPullbackFstIso f x₀).symm) ≪≫
        fiberSingularHomologyIsoOfPath (mem_serreFibrations_pullbackFst hp f) M γ' n ≪≫
        F.mapIso (p.fiberPullbackFstIso f x₁ ≪≫ eqToIso (congrArg p.fiber hb₁)) := by
  let F := (singularHomologyFunctor (ModuleCat.{u} R) n).obj M
  let I := _root_.TopCat.of (ULift.{u} unitInterval)
  let p_f := _root_.TopCat.pullbackFst f p
  have hp_f : serreFibrations p_f := mem_serreFibrations_pullbackFst hp f
  let g' : I ⟶ B' :=
    _root_.TopCat.ofHom ⟨fun t ↦ γ' t.down, γ'.continuous.comp continuous_uliftDown⟩
  let g : I ⟶ B := _root_.TopCat.ofHom ⟨fun t ↦ γ t.down, γ.continuous.comp continuous_uliftDown⟩
  let p'_f := _root_.TopCat.pullbackFst g' p_f
  let p' := _root_.TopCat.pullbackFst g p
  have hp'_f : serreFibrations p'_f := mem_serreFibrations_pullbackFst hp_f g'
  have hp' : serreFibrations p' := mem_serreFibrations_pullbackFst hp g
  let t₀ : I := ULift.up (0 : unitInterval)
  let t₁ : I := ULift.up (1 : unitInterval)
  have : IsIso (F.map (p'_f.fiberι t₀)) :=
    isIso_singularHomologyMap_fiberι_of_contractibleSpace hp'_f M t₀ n
  have : IsIso (F.map (p'_f.fiberι t₁)) :=
    isIso_singularHomologyMap_fiberι_of_contractibleSpace hp'_f M t₁ n
  have : IsIso (F.map (p'.fiberι t₀)) :=
    isIso_singularHomologyMap_fiberι_of_contractibleSpace hp' M t₀ n
  have : IsIso (F.map (p'.fiberι t₁)) :=
    isIso_singularHomologyMap_fiberι_of_contractibleSpace hp' M t₁ n
  have heq : ∀ {y y' : B} (_ : y = y') (h : p.fiber y = p.fiber y') (z : p.fiber y),
      (eqToHom h z : E) = (z : E) := by
    intro _ _ hy h _
    subst hy
    rw [Subsingleton.elim h rfl, eqToHom_refl]
    rfl
  have heq_pf : ∀ {y y' : B'} (_ : y = y') (h : p_f.fiber y = p_f.fiber y') (z : p_f.fiber y),
      (eqToHom h z).1.1.2 = z.1.1.2 := by
    intro _ _ hy h _
    subst hy
    rw [Subsingleton.elim h rfl, eqToHom_refl]
    rfl
  let Φ : _root_.TopCat.of { q : I × _root_.TopCat.of { r : B' × E // f r.1 = p r.2 } //
        g' q.1 = p_f q.2 } ⟶
      _root_.TopCat.of { q : I × E // g q.1 = p q.2 } :=
    _root_.TopCat.ofHom
      { toFun q := ⟨(q.1.1, q.1.2.1.2),
          (hγ q.1.1.down).symm.trans ((congrArg f q.2).trans q.1.2.2)⟩
        continuous_toFun := by
          refine Continuous.subtype_mk (Continuous.prodMk ?_ ?_) _
          · exact continuous_fst.comp continuous_subtype_val
          · exact continuous_snd.comp
              (continuous_subtype_val.comp (continuous_snd.comp continuous_subtype_val)) }
  have hΦ (t : I) :
      p'_f.fiberι t ≫ Φ =
        (p_f.fiberPullbackFstIso g' t).hom ≫ (p.fiberPullbackFstIso f (g' t)).hom ≫
          eqToHom (congrArg p.fiber (hγ t.down)) ≫ (p.fiberPullbackFstIso g t).inv ≫
          p'.fiberι t := by
    refine _root_.TopCat.ext fun x ↦ Subtype.ext ?_
    simp only [ConcreteCategory.comp_apply]
    rw [p'_f.fiberι_apply, p'.fiberι_apply, p.fiberPullbackFstIso_inv_apply_coe]
    refine Prod.ext (p'_f.apply_coe_fiber t x) ?_
    change x.1.1.2.1.2 =
      (eqToHom (congrArg p.fiber (hγ t.down))
        ((p.fiberPullbackFstIso f (g' t)).hom ((p_f.fiberPullbackFstIso g' t).hom x)) : E)
    rw [heq (hγ t.down), p.fiberPullbackFstIso_hom_apply_coe]
    exact (congrArg (fun r ↦ r.1.2) (p_f.fiberPullbackFstIso_hom_apply_coe g' t x)).symm
  let ψ (t : I) : p'_f.fiber t ≅ p'.fiber t :=
    p_f.fiberPullbackFstIso g' t ≪≫ p.fiberPullbackFstIso f (g' t) ≪≫
      eqToIso (congrArg p.fiber (hγ t.down)) ≪≫ (p.fiberPullbackFstIso g t).symm
  have hψ_map (t : I) :
      F.map (p'_f.fiberι t) ≫ F.map Φ = F.map (ψ t).hom ≫ F.map (p'.fiberι t) := by
    rw [← F.map_comp, hΦ t]
    simp [ψ]
  have hmid :
      F.map (p'.fiberι t₀) ≫ (asIso (F.map (p'.fiberι t₁))).inv =
        F.map (ψ t₀).inv ≫ F.map (p'_f.fiberι t₀) ≫
          (asIso (F.map (p'_f.fiberι t₁))).inv ≫ F.map (ψ t₁).hom := by
    refine (cancel_mono (F.map (p'.fiberι t₁))).1 ?_
    simp only [asIso_inv, Category.assoc, IsIso.inv_hom_id, Category.comp_id, ← hψ_map t₁]
    simp only [← Category.assoc]
    have hcancel :
        F.map (ψ t₀).inv ≫ F.map (p'_f.fiberι t₀) ≫
            (inv (F.map (p'_f.fiberι t₁)) ≫ F.map (p'_f.fiberι t₁)) ≫ F.map Φ =
          F.map (p'.fiberι t₀) := by
      rw [IsIso.inv_hom_id, Category.id_comp, hψ_map t₀, ← Category.assoc, ← F.map_comp,
        Iso.inv_hom_id, F.map_id, Category.id_comp]
    simpa only [Category.assoc] using hcancel.symm
  have hleft :
      eqToIso (congrArg p.fiber hb₀.symm) ≪≫ (p.fiberPullbackFstIso f x₀).symm ≪≫
          eqToIso (congrArg p_f.fiber γ'.source.symm) ≪≫
          (p_f.fiberPullbackFstIso g' t₀).symm =
        eqToIso (congrArg p.fiber γ.source.symm) ≪≫
          (p.fiberPullbackFstIso g t₀).symm ≪≫ (ψ t₀).symm := by
    suffices (eqToIso (congrArg p.fiber hb₀.symm) ≪≫ (p.fiberPullbackFstIso f x₀).symm ≪≫
          eqToIso (congrArg p_f.fiber γ'.source.symm) ≪≫
          (p_f.fiberPullbackFstIso g' t₀).symm).symm =
        (eqToIso (congrArg p.fiber γ.source.symm) ≪≫
          (p.fiberPullbackFstIso g t₀).symm ≪≫ (ψ t₀).symm).symm by
      simpa using congrArg Iso.symm this
    apply Iso.ext
    refine _root_.TopCat.ext fun z ↦ Subtype.ext ?_
    simp only [ψ, Iso.trans_symm, Iso.trans_hom, Iso.symm_hom, Iso.symm_inv, eqToIso.inv,
      eqToIso.hom, Category.assoc, Iso.inv_hom_id_assoc, ConcreteCategory.comp_apply]
    rw [heq hb₀, p.fiberPullbackFstIso_hom_apply_coe, heq_pf (γ'.source : g' t₀ = x₀),
      heq (γ.source : g t₀ = b₀), heq (hγ t₀.down), p.fiberPullbackFstIso_hom_apply_coe]
  have hright :
      p_f.fiberPullbackFstIso g' t₁ ≪≫ eqToIso (congrArg p_f.fiber γ'.target) ≪≫
          p.fiberPullbackFstIso f x₁ ≪≫ eqToIso (congrArg p.fiber hb₁) =
        ψ t₁ ≪≫ p.fiberPullbackFstIso g t₁ ≪≫ eqToIso (congrArg p.fiber γ.target) := by
    apply Iso.ext
    refine _root_.TopCat.ext fun z ↦ Subtype.ext ?_
    simp only [ψ, Iso.trans_hom, Iso.symm_hom, eqToIso.hom, Category.assoc, Iso.inv_hom_id_assoc,
      ConcreteCategory.comp_apply]
    rw [heq hb₁, p.fiberPullbackFstIso_hom_apply_coe, heq_pf (γ'.target : g' t₁ = x₁),
      heq (γ.target : g t₁ = b₁), heq (hγ t₁.down), p.fiberPullbackFstIso_hom_apply_coe]
  apply Iso.ext
  change F.map (eqToIso (congrArg p.fiber γ.source.symm) ≪≫
        (p.fiberPullbackFstIso g t₀).symm).hom ≫
      F.map (p'.fiberι t₀) ≫ (asIso (F.map (p'.fiberι t₁))).inv ≫
      F.map (p.fiberPullbackFstIso g t₁ ≪≫ eqToIso (congrArg p.fiber γ.target)).hom =
    F.map (eqToIso (congrArg p.fiber hb₀.symm) ≪≫ (p.fiberPullbackFstIso f x₀).symm).hom ≫
      (F.map (eqToIso (congrArg p_f.fiber γ'.source.symm) ≪≫
          (p_f.fiberPullbackFstIso g' t₀).symm).hom ≫
        F.map (p'_f.fiberι t₀) ≫ (asIso (F.map (p'_f.fiberι t₁))).inv ≫
        F.map (p_f.fiberPullbackFstIso g' t₁ ≪≫ eqToIso (congrArg p_f.fiber γ'.target)).hom) ≫
      F.map (p.fiberPullbackFstIso f x₁ ≪≫ eqToIso (congrArg p.fiber hb₁)).hom
  simp only [Iso.trans_hom, Iso.symm_hom, F.map_comp, Category.assoc]
  rw [reassoc_of% hmid]
  have hl := congrArg (fun e : p.fiber b₀ ≅ p'_f.fiber t₀ ↦ F.map e.hom) hleft
  have hr := congrArg (fun e : p'_f.fiber t₁ ≅ p.fiber b₁ ↦ F.map e.hom) hright
  simp only [Iso.trans_hom, Iso.symm_hom, F.map_comp] at hl hr
  rw [hr]
  simp only [← Category.assoc] at hl ⊢
  rw [hl]

/-- Path transport along the constant path `Path.refl b` is the identity isomorphism. -/
@[simp]
theorem fiberSingularHomologyIsoOfPath_refl (b : B) (n : ℕ) :
    fiberSingularHomologyIsoOfPath hp M (Path.refl b) n = Iso.refl _ := by
  let B' := _root_.TopCat.of PUnit.{u + 1}
  let f : B' ⟶ B := _root_.TopCat.ofHom (ContinuousMap.const _ b)
  have : ContractibleSpace B' := inferInstanceAs (ContractibleSpace PUnit.{u + 1})
  rw [fiberSingularHomologyIsoOfPath_pullbackFst hp M f (Path.refl PUnit.unit) (Path.refl b)
      rfl rfl (fun _ ↦ rfl) n,
    fiberSingularHomologyIsoOfPath_eq_of_contractibleSpace
      (mem_serreFibrations_pullbackFst hp f) M (Path.refl PUnit.unit) n]
  ext
  simp

/-- Path transport along the reversed path `γ.symm` is the inverse isomorphism. -/
@[simp]
theorem fiberSingularHomologyIsoOfPath_symm {b₀ b₁ : B} (γ : Path b₀ b₁) (n : ℕ) :
    fiberSingularHomologyIsoOfPath hp M γ.symm n =
      (fiberSingularHomologyIsoOfPath hp M γ n).symm := by
  let B' := _root_.TopCat.of (ULift.{u} unitInterval)
  let f : B' ⟶ B := _root_.TopCat.ofHom ⟨fun t ↦ γ t.down, γ.continuous.comp continuous_uliftDown⟩
  let ι : Path (ULift.up (0 : unitInterval)) (ULift.up (1 : unitInterval)) :=
    { toFun := ULift.up
      continuous_toFun := continuous_uliftUp
      source' := rfl
      target' := rfl }
  rw [fiberSingularHomologyIsoOfPath_pullbackFst hp M f ι γ γ.source γ.target (fun _ ↦ rfl) n,
    fiberSingularHomologyIsoOfPath_pullbackFst hp M f ι.symm γ.symm γ.target γ.source
      (fun _ ↦ rfl) n,
    fiberSingularHomologyIsoOfPath_eq_of_contractibleSpace
      (mem_serreFibrations_pullbackFst hp f) M ι n,
    fiberSingularHomologyIsoOfPath_eq_of_contractibleSpace
      (mem_serreFibrations_pullbackFst hp f) M ι.symm n]
  ext
  simp

/-- Path transport along a concatenation `γ.trans δ` is the composition of the path transport
isomorphisms along `γ` and `δ`. -/
theorem fiberSingularHomologyIsoOfPath_trans {b₀ b₁ b₂ : B} (γ : Path b₀ b₁) (δ : Path b₁ b₂)
    (n : ℕ) :
    fiberSingularHomologyIsoOfPath hp M (γ.trans δ) n =
      fiberSingularHomologyIsoOfPath hp M γ n ≪≫ fiberSingularHomologyIsoOfPath hp M δ n := by
  let B' := _root_.TopCat.of (ULift.{u} unitInterval)
  let f : B' ⟶ B := _root_.TopCat.ofHom
    ⟨fun t ↦ (γ.trans δ) t.down, (γ.trans δ).continuous.comp continuous_uliftDown⟩
  let x₀ : B' := ULift.up (0 : unitInterval)
  let x₁ : B' := ULift.up ⟨1 / 2, by constructor <;> norm_num⟩
  let x₂ : B' := ULift.up (1 : unitInterval)
  have hfx₁ : f x₁ = b₁ := by
    change (γ.trans δ) ⟨1 / 2, _⟩ = b₁
    rw [Path.trans_apply]
    split_ifs with ht
    · convert γ.target
      norm_num
    · exfalso
      norm_num at ht
  let ι : Path x₀ x₂ :=
    { toFun := ULift.up
      continuous_toFun := continuous_uliftUp
      source' := rfl
      target' := rfl }
  let ι₁ : Path x₀ x₁ :=
    { toFun t := ULift.up ⟨(t : ℝ) / 2, ⟨by linarith [t.2.1], by linarith [t.2.2]⟩⟩
      continuous_toFun := continuous_uliftUp.comp <|
        Continuous.subtype_mk (continuous_subtype_val.div_const 2) _
      source' := by ext; simp [x₀]
      target' := by ext; simp [x₁] }
  let ι₂ : Path x₁ x₂ :=
    { toFun t := ULift.up ⟨((t : ℝ) + 1) / 2, ⟨by linarith [t.2.1], by linarith [t.2.2]⟩⟩
      continuous_toFun := continuous_uliftUp.comp <|
        Continuous.subtype_mk ((continuous_subtype_val.add continuous_const).div_const 2) _
      source' := by ext; simp [x₁]
      target' := by ext; norm_num [x₂] }
  have hι₁ (t : unitInterval) : f (ι₁ t) = γ t := by
    change (γ.trans δ) ⟨(t : ℝ) / 2, _⟩ = γ t
    rw [Path.trans_apply]
    split_ifs with ht
    · congr 1
      ext
      ring
    · exfalso
      linarith [t.2.2]
  have hι₂ (t : unitInterval) : f (ι₂ t) = δ t := by
    change (γ.trans δ) ⟨((t : ℝ) + 1) / 2, _⟩ = δ t
    rw [Path.trans_apply]
    split_ifs with ht
    · have ht0 : (t : ℝ) = 0 := by linarith [t.2.1]
      have ht' : t = 0 := Subtype.ext ht0
      subst ht'
      convert γ.target.trans δ.source.symm
      norm_num
    · congr 1
      ext
      ring
  rw [fiberSingularHomologyIsoOfPath_pullbackFst hp M f ι (γ.trans δ) (γ.trans δ).source
      (γ.trans δ).target (fun _ ↦ rfl) n,
    fiberSingularHomologyIsoOfPath_pullbackFst hp M f ι₁ γ (γ.trans δ).source hfx₁ hι₁ n,
    fiberSingularHomologyIsoOfPath_pullbackFst hp M f ι₂ δ hfx₁ (γ.trans δ).target hι₂ n,
    fiberSingularHomologyIsoOfPath_eq_of_contractibleSpace
      (mem_serreFibrations_pullbackFst hp f) M ι n,
    fiberSingularHomologyIsoOfPath_eq_of_contractibleSpace
      (mem_serreFibrations_pullbackFst hp f) M ι₁ n,
    fiberSingularHomologyIsoOfPath_eq_of_contractibleSpace
      (mem_serreFibrations_pullbackFst hp f) M ι₂ n]
  ext
  simp

/-- Homotopic paths with fixed endpoints induce the same isomorphism on the singular homology of the
fibres. -/
theorem fiberSingularHomologyIsoOfPath_congr {b₀ b₁ : B} {γ₀ γ₁ : Path b₀ b₁}
    (h : γ₀.Homotopic γ₁) (n : ℕ) :
    fiberSingularHomologyIsoOfPath hp M γ₀ n = fiberSingularHomologyIsoOfPath hp M γ₁ n := by
  obtain ⟨H⟩ := h
  let B' := _root_.TopCat.of (ULift.{u} (unitInterval × unitInterval))
  let f : B' ⟶ B := _root_.TopCat.ofHom ⟨fun x ↦ H x.down, H.continuous.comp continuous_uliftDown⟩
  let q₀₀ : B' := ULift.up (0, 0)
  let q₀₁ : B' := ULift.up (0, 1)
  let q₁₀ : B' := ULift.up (1, 0)
  let q₁₁ : B' := ULift.up (1, 1)
  have hq₀₀ : f q₀₀ = b₀ := (H.apply_zero 0).trans γ₀.source
  have hq₀₁ : f q₀₁ = b₁ := (H.apply_zero 1).trans γ₀.target
  have hq₁₀ : f q₁₀ = b₀ := (H.apply_one 0).trans γ₁.source
  have hq₁₁ : f q₁₁ = b₁ := (H.apply_one 1).trans γ₁.target
  let α₀ : Path q₀₀ q₀₁ :=
    { toFun t := ULift.up (0, t)
      continuous_toFun := continuous_uliftUp.comp (continuous_const.prodMk continuous_id)
      source' := rfl
      target' := rfl }
  let α₁ : Path q₁₀ q₁₁ :=
    { toFun t := ULift.up (1, t)
      continuous_toFun := continuous_uliftUp.comp (continuous_const.prodMk continuous_id)
      source' := rfl
      target' := rfl }
  let c₀ : Path q₀₀ q₁₀ :=
    { toFun s := ULift.up (s, 0)
      continuous_toFun := continuous_uliftUp.comp (continuous_id.prodMk continuous_const)
      source' := rfl
      target' := rfl }
  let c₁ : Path q₀₁ q₁₁ :=
    { toFun s := ULift.up (s, 1)
      continuous_toFun := continuous_uliftUp.comp (continuous_id.prodMk continuous_const)
      source' := rfl
      target' := rfl }
  have hsq :
      fiberSingularHomologyIsoOfPath hp M γ₀ n ≪≫
          fiberSingularHomologyIsoOfPath hp M (Path.refl b₁) n =
        fiberSingularHomologyIsoOfPath hp M (Path.refl b₀) n ≪≫
          fiberSingularHomologyIsoOfPath hp M γ₁ n := by
    rw [fiberSingularHomologyIsoOfPath_pullbackFst hp M f α₀ γ₀ hq₀₀ hq₀₁
        (fun t ↦ H.apply_zero t) n,
      fiberSingularHomologyIsoOfPath_pullbackFst hp M f c₁ (Path.refl b₁) hq₀₁ hq₁₁
        (fun s ↦ (H.prop' s 1 (Or.inr rfl)).trans γ₀.target) n,
      fiberSingularHomologyIsoOfPath_pullbackFst hp M f c₀ (Path.refl b₀) hq₀₀ hq₁₀
        (fun s ↦ (H.prop' s 0 (Or.inl rfl)).trans γ₀.source) n,
      fiberSingularHomologyIsoOfPath_pullbackFst hp M f α₁ γ₁ hq₁₀ hq₁₁
        (fun t ↦ H.apply_one t) n,
      fiberSingularHomologyIsoOfPath_eq_of_contractibleSpace
        (mem_serreFibrations_pullbackFst hp f) M α₀ n,
      fiberSingularHomologyIsoOfPath_eq_of_contractibleSpace
        (mem_serreFibrations_pullbackFst hp f) M c₁ n,
      fiberSingularHomologyIsoOfPath_eq_of_contractibleSpace
        (mem_serreFibrations_pullbackFst hp f) M c₀ n,
      fiberSingularHomologyIsoOfPath_eq_of_contractibleSpace
        (mem_serreFibrations_pullbackFst hp f) M α₁ n]
    ext
    simp
  rw [fiberSingularHomologyIsoOfPath_refl, fiberSingularHomologyIsoOfPath_refl,
    Iso.trans_refl, Iso.refl_trans] at hsq
  exact hsq

end PathTransport

end TauCeti.TopCat
