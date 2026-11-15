/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.SingularHomology.HomotopyInvariance
public import Mathlib.Analysis.Convex.Contractible
public import TauCeti.AlgebraicTopology.LocalCoefficient
public import TauCeti.AlgebraicTopology.Singular.Homotopy.WeakHomotopyEquivalence
public import TauCeti.Topology.Category.TopCat.Pullback
public import TauCeti.Topology.Homotopy.HomotopyGroup.HomotopyEquiv
public import TauCeti.Topology.Homotopy.HurewiczFibration.Transport
public import TauCeti.Topology.Homotopy.SerreFibration.Connected

/-!
# The local system of fibre homology of a Serre fibration

Let `p : E → B` be a Serre fibration (`TauCeti.TopCat.serreFibrations`) and `M` a module over a
ring `R`. The singular homology groups `H_n(p⁻¹(b); M)` of the fibres form a local coefficient
system on `B` (`TauCeti.TopCat.serreFiberLocalSystem`): a path `γ` from `b₀` to `b₁` acts by the
**transport** `H_n(p⁻¹(b₀); M) → H_n(p⁻¹(b₁); M)` along `γ` (`TauCeti.TopCat.serreTransport`).
This is the coefficient system of the second page `E²_{s,t} = H_s(B; H_t(F; M))` of the Serre
spectral sequence.

A Serre fibration lifts homotopies of disks only, so there is no transport map between the fibres
themselves. The transport is defined on homology instead, through the base change of `p` along a
map from a contractible space. For `f : K → B` with `K` contractible, the base change
`K ×_B E → K` is a Serre fibration over a contractible base, so the inclusion of each of its
fibres `p⁻¹(f k) → K ×_B E`, `x ↦ (k, x)` (`TauCeti.TopCat.fiberToPullback`), is a weak homotopy
equivalence, by the exact homotopy sequence. It is therefore an isomorphism on singular homology
(`TauCeti.TopCat.isIso_singularHomologyMap_fiberToPullback`), and any two points `k₀, k₁` of `K`
give an isomorphism `H_n(p⁻¹(f k₀); M) → H_n(p⁻¹(f k₁); M)` through `H_n(K ×_B E; M)`
(`TauCeti.TopCat.fiberHomologyTransport`). The transport along a path `γ` is the case of the
interval `K = I`, `f = γ`. Parametrizing by squares shows that it depends only on the homotopy
class of `γ`, and parametrizing by the two halves of the interval that it is compatible with
concatenation.

The local system is natural in the coefficients (`TauCeti.TopCat.serreFiberLocalSystemMapCoeff`)
and in maps of fibrations (`CategoryTheory.CommSq.serreFiberLocalSystemMap`). For a Hurewicz
fibration with a lifting function `Λ`, the transport is the map induced on homology by the
transport `Λ.transport γ` of points along lifts of `γ`
(`TauCeti.TopCat.serreTransport_eq_map_transport`), as in the local system of fibre homology of a
Hurewicz fibration, `TauCeti.fiberLocalSystem`.

## Main definitions

* `TauCeti.TopCat.fiberToPullback f p h`: the inclusion of a fibre of `p` into the base change of
  `p` along `f`.
* `TauCeti.TopCat.fiberHomologyTransport hp M n f h₀ h₁`: the transport between the homology of
  the fibres over two points of a contractible space mapped to `B`.
* `TauCeti.TopCat.serreTransport hp M n γ`: the transport along a path.
* `TauCeti.TopCat.serreFiberLocalSystem hp M n`: the local system `b ↦ H_n(p⁻¹(b); M)`.

## Main results

* `TauCeti.TopCat.isIso_singularHomologyMap_fiberToPullback`: over a contractible space, the
  fibre inclusions into the base change are isomorphisms on singular homology.
* `TauCeti.TopCat.serreTransport_map`: the transport along the image of a path in a contractible
  space `K` is the transport through `K`.
* `TauCeti.TopCat.serreTransport_congr`, `TauCeti.TopCat.serreTransport_refl`,
  `TauCeti.TopCat.serreTransport_trans`: the transport depends only on the homotopy class of the
  path, and is compatible with constant paths and concatenation.
* `TauCeti.TopCat.serreTransport_eq_map_transport`: for a Hurewicz fibration, the transport is
  induced by the transport of points along lifts of paths.

## References

* J.-P. Serre, *Homologie singulière des espaces fibrés. Applications*, Ann. of Math. 54 (1951),
  425–505, Chapter II.
* A. Hatcher, *Algebraic Topology*, Section 4.2, Proposition 4.61, and Section 3.H.
* J. McCleary, *A User's Guide to Spectral Sequences*, second edition, Chapter 5.
-/

public section

noncomputable section

open CategoryTheory AlgebraicTopology unitInterval

universe v u

namespace TauCeti.TopCat

variable {E B K K' : TopCat.{u}} {p : E ⟶ B}

/-! ### Fibres in a base change -/

/-- The inclusion `x ↦ (k, x)` of the fibre of `p : E ⟶ B` over `b` into the base change
`K ×_B E = {(k, e) | f k = p e}` of `p` along `f : K ⟶ B`, at a point `k` of `K` over `b`. -/
def fiberToPullback (f : K ⟶ B) (p : E ⟶ B) {k : K} {b : B} (h : f k = b) :
    p.fiber b ⟶ _root_.TopCat.of {x : K × E // f x.1 = p x.2} :=
  _root_.TopCat.ofHom ⟨fun x ↦ ⟨(k, x.1), h.trans (Set.mem_singleton_iff.1 x.2).symm⟩,
    (continuous_const.prodMk continuous_subtype_val).subtype_mk _⟩

@[simp]
lemma fiberToPullback_hom_apply_coe (f : K ⟶ B) (p : E ⟶ B) {k : K} {b : B} (h : f k = b)
    (x : p.fiber b) : ((fiberToPullback f p h).hom x : K × E) = (k, x.1) :=
  (rfl)

/-- At a point `k`, the fibre inclusion into the base change is the fibre inclusion of the base
change over `k`, after the identification `TopCat.Hom.fiberPullbackFstIso` of the fibres. -/
lemma fiberToPullback_eq (f : K ⟶ B) (p : E ⟶ B) (k : K) :
    fiberToPullback f p (rfl : f k = f k) =
      (p.fiberPullbackFstIso f k).inv ≫ (_root_.TopCat.pullbackFst f p).fiberι k := by
  ext x : 1
  apply Subtype.ext
  rw [ConcreteCategory.comp_apply, TopCat.Hom.fiberι_apply,
    TopCat.Hom.fiberPullbackFstIso_inv_apply_coe]
  rfl

/-- The map of base changes `K' ×_B E → K ×_B E` induced by a map `φ : K' ⟶ K` over `B`. -/
private def pullbackMapOfComp (φ : K' ⟶ K) (f : K ⟶ B) (p : E ⟶ B) :
    _root_.TopCat.of {x : K' × E // (φ ≫ f) x.1 = p x.2} ⟶
      _root_.TopCat.of {x : K × E // f x.1 = p x.2} :=
  _root_.TopCat.ofHom ⟨fun x ↦ ⟨(φ x.1.1, x.1.2), x.2⟩,
    ((φ.hom.continuous.comp (continuous_fst.comp continuous_subtype_val)).prodMk
      (continuous_snd.comp continuous_subtype_val)).subtype_mk _⟩

@[reassoc]
private lemma fiberToPullback_comp_pullbackMapOfComp (φ : K' ⟶ K) (f : K ⟶ B) (p : E ⟶ B) {k : K'}
    {b : B} (h : (φ ≫ f) k = b) :
    fiberToPullback (φ ≫ f) p h ≫ pullbackMapOfComp φ f p = fiberToPullback f p (k := φ k) h :=
  (rfl)

end TauCeti.TopCat

namespace CategoryTheory.CommSq

open TauCeti.TopCat

variable {E B E' B' K : TopCat.{u}} {p : E ⟶ B} {p' : E' ⟶ B'} {g : E ⟶ E'} {c : B ⟶ B'}

/-- The map of base changes `K ×_B E → K ×_{B'} E'` along `f` and `f ≫ c`, `(k, e) ↦ (k, g e)`,
induced by a commutative square `g ≫ p' = p ≫ c`, that is, by a map of fibrations. -/
private def pullbackMap (sq : CommSq g p p' c) (f : K ⟶ B) :
    TopCat.of {x : K × E // f x.1 = p x.2} ⟶ TopCat.of {x : K × E' // (f ≫ c) x.1 = p' x.2} :=
  TopCat.ofHom ⟨fun x ↦ ⟨(x.1.1, g x.1.2),
      (congrArg c x.2).trans (ConcreteCategory.congr_hom sq.w x.1.2).symm⟩,
    ((continuous_fst.comp continuous_subtype_val).prodMk
      (g.hom.continuous.comp (continuous_snd.comp continuous_subtype_val))).subtype_mk _⟩

@[reassoc]
private lemma fiberToPullback_comp_pullbackMap (sq : CommSq g p p' c) (f : K ⟶ B) {k : K} {b : B}
    (h : f k = b) :
    fiberToPullback f p h ≫ sq.pullbackMap f =
      sq.fiberMap b ≫ fiberToPullback (f ≫ c) p' (k := k) (congrArg c h) := by
  ext x : 1
  exact Subtype.ext (Prod.ext rfl (sq.fiberMap_apply_coe b x).symm)

end CategoryTheory.CommSq

namespace TauCeti.TopCat

variable {E B K K' : TopCat.{u}} {p : E ⟶ B}

/-! ### Transport through a contractible space -/

section Transport

variable (hp : serreFibrations p) {R : Type v} [Ring R] (M : ModuleCat.{u} R) (n : ℕ)

include hp in
/-- **The fibres of a Serre fibration are homologically the base change over a contractible
space.** For a Serre fibration `p : E ⟶ B` and a map `f : K ⟶ B` from a contractible space, the
inclusion `x ↦ (k, x)` of the fibre of `p` over `f k` into the base change `K ×_B E` induces
isomorphisms on singular homology with coefficients in any module. -/
theorem isIso_singularHomologyMap_fiberToPullback (f : K ⟶ B) [ContractibleSpace K] {k : K}
    {b : B} (h : f k = b) :
    IsIso (((singularHomologyFunctor (ModuleCat.{u} R) n).obj M).map (fiberToPullback f p h)) := by
  subst h
  -- The fibre inclusion of the base change over `k` is `n`-connected for every `n`, by the exact
  -- homotopy sequence of the base change over its contractible base.
  have hwe : ((_root_.TopCat.pullbackFst f p).fiberι k).hom.IsWeakHomotopyEquivalence :=
    ContinuousMap.isWeakHomotopyEquivalence_iff_forall_isNConnected.2 fun _ ↦
      isNConnected_fiberι_of_mem_serreFibrations (mem_serreFibrations_pullbackFst hp f)
        fun _ _ ↦ inferInstance
  have := hwe.isIso_singularHomologyMap M n
  rw [_root_.TopCat.ofHom_hom] at this
  rw [fiberToPullback_eq, Functor.map_comp]
  infer_instance

/-- The **transport through a contractible space**. For a Serre fibration `p : E ⟶ B`, a map
`f : K ⟶ B` from a contractible space and two points `k₀`, `k₁` of `K` over `b₀`, `b₁`, the
isomorphism `H_n(p⁻¹(b₀); M) → H_n(p⁻¹(b₁); M)` through the homology of the base change `K ×_B E`,
into which both fibres include by isomorphisms
(`TauCeti.TopCat.isIso_singularHomologyMap_fiberToPullback`). -/
def fiberHomologyTransport (f : K ⟶ B) [ContractibleSpace K] {k₀ k₁ : K} {b₀ b₁ : B}
    (h₀ : f k₀ = b₀) (h₁ : f k₁ = b₁) :
    ((singularHomologyFunctor (ModuleCat.{u} R) n).obj M).obj (p.fiber b₀) ⟶
      ((singularHomologyFunctor (ModuleCat.{u} R) n).obj M).obj (p.fiber b₁) :=
  haveI := isIso_singularHomologyMap_fiberToPullback hp M n f h₁
  ((singularHomologyFunctor (ModuleCat.{u} R) n).obj M).map (fiberToPullback f p h₀) ≫
    inv (((singularHomologyFunctor (ModuleCat.{u} R) n).obj M).map (fiberToPullback f p h₁))

/-- The transport through `K` depends on the map to `B` and on the points of `K` only through
their equality. -/
theorem fiberHomologyTransport_congr {f₁ f₂ : K ⟶ B} [ContractibleSpace K] (hf : f₁ = f₂)
    {k₀ k₁ k₀' k₁' : K} (e₀ : k₀ = k₀') (e₁ : k₁ = k₁') {b₀ b₁ : B} (h₀ : f₁ k₀ = b₀)
    (h₁ : f₁ k₁ = b₁) (h₀' : f₂ k₀' = b₀) (h₁' : f₂ k₁' = b₁) :
    fiberHomologyTransport hp M n f₁ h₀ h₁ = fiberHomologyTransport hp M n f₂ h₀' h₁' := by
  subst hf e₀ e₁
  rfl

variable (f : K ⟶ B) [ContractibleSpace K] {k₀ k₁ k₂ : K} {b₀ b₁ b₂ : B}

/-- The transport through `K`, followed by the inclusion of the target fibre into `K ×_B E`, is
the inclusion of the source fibre. -/
@[reassoc (attr := simp)]
theorem fiberHomologyTransport_comp_map (h₀ : f k₀ = b₀) (h₁ : f k₁ = b₁) :
    fiberHomologyTransport hp M n f h₀ h₁ ≫
        ((singularHomologyFunctor (ModuleCat.{u} R) n).obj M).map (fiberToPullback f p h₁) =
      ((singularHomologyFunctor (ModuleCat.{u} R) n).obj M).map (fiberToPullback f p h₀) := by
  have := isIso_singularHomologyMap_fiberToPullback hp M n f h₁
  simp [fiberHomologyTransport]

/-- The transport through `K` is the unique map whose composite with the inclusion of the target
fibre into `K ×_B E` is the inclusion of the source fibre. -/
theorem eq_fiberHomologyTransport_iff (h₀ : f k₀ = b₀) (h₁ : f k₁ = b₁)
    (φ : ((singularHomologyFunctor (ModuleCat.{u} R) n).obj M).obj (p.fiber b₀) ⟶
      ((singularHomologyFunctor (ModuleCat.{u} R) n).obj M).obj (p.fiber b₁)) :
    φ = fiberHomologyTransport hp M n f h₀ h₁ ↔
      φ ≫ ((singularHomologyFunctor (ModuleCat.{u} R) n).obj M).map (fiberToPullback f p h₁) =
        ((singularHomologyFunctor (ModuleCat.{u} R) n).obj M).map (fiberToPullback f p h₀) := by
  have := isIso_singularHomologyMap_fiberToPullback hp M n f h₁
  rw [← fiberHomologyTransport_comp_map hp M n f h₀ h₁, cancel_mono]

instance isIso_fiberHomologyTransport (h₀ : f k₀ = b₀) (h₁ : f k₁ = b₁) :
    IsIso (fiberHomologyTransport hp M n f h₀ h₁) := by
  have := isIso_singularHomologyMap_fiberToPullback hp M n f h₀
  have := isIso_singularHomologyMap_fiberToPullback hp M n f h₁
  unfold fiberHomologyTransport
  infer_instance

/-- The transport through `K` from a point to itself is the identity. -/
@[simp]
theorem fiberHomologyTransport_self (h₀ h₁ : f k₀ = b₀) :
    fiberHomologyTransport hp M n f h₀ h₁ = 𝟙 _ :=
  ((eq_fiberHomologyTransport_iff hp M n f h₀ h₁ _).2 (Category.id_comp _)).symm

/-- Transport through `K` is compatible with composition. -/
@[reassoc (attr := simp)]
theorem fiberHomologyTransport_comp (h₀ : f k₀ = b₀) (h₁ : f k₁ = b₁) (h₂ : f k₂ = b₂) :
    fiberHomologyTransport hp M n f h₀ h₁ ≫ fiberHomologyTransport hp M n f h₁ h₂ =
      fiberHomologyTransport hp M n f h₀ h₂ :=
  (eq_fiberHomologyTransport_iff hp M n f h₀ h₂ _).2 (by simp)

/-- **Transport along a path in a fibre of `f` is the identity.** If `k₀` and `k₁` are joined by
a path in `K` which `f` maps to the point `b`, the transport through `K` from `k₀` to `k₁` is the
identity of `H_n(p⁻¹(b); M)`. -/
theorem fiberHomologyTransport_eq_id_of_path (δ : Path k₀ k₁) (hδ : ∀ t, f (δ t) = b₀)
    (h₀ : f k₀ = b₀) (h₁ : f k₁ = b₀) : fiberHomologyTransport hp M n f h₀ h₁ = 𝟙 _ := by
  refine ((eq_fiberHomologyTransport_iff hp M n f h₀ h₁ _).2 ?_).symm
  rw [Category.id_comp]
  -- The fibre inclusions at `k₀` and `k₁` are homotopic, through the fibre inclusions along `δ`.
  let H : _root_.TopCat.Homotopy (fiberToPullback f p h₁) (fiberToPullback f p h₀) :=
    { toFun z := ⟨(δ (σ z.1), z.2.1), (hδ _).trans (Set.mem_singleton_iff.1 z.2.2).symm⟩
      continuous_toFun := by fun_prop
      -- The second components agree by definition of `fiberToPullback`.
      map_zero_left x := Subtype.ext (Prod.ext (by simp : δ (σ 0) = k₁) rfl)
      map_one_left x := Subtype.ext (Prod.ext (by simp : δ (σ 1) = k₀) rfl) }
  exact TopCat.Homotopy.congr_homologyMap_singularChainComplexFunctor H M n

/-- **Base change of the parameter space.** For `φ : K' ⟶ K` between contractible spaces, the
transport through `K'` along `φ ≫ f` is the transport through `K` along `f`. -/
theorem fiberHomologyTransport_comp_left (φ : K' ⟶ K) [ContractibleSpace K'] {k₀ k₁ : K'}
    (h₀ : (φ ≫ f) k₀ = b₀) (h₁ : (φ ≫ f) k₁ = b₁) :
    fiberHomologyTransport hp M n (φ ≫ f) h₀ h₁ =
      fiberHomologyTransport hp M n f (k₀ := φ k₀) (k₁ := φ k₁) h₀ h₁ := by
  rw [eq_fiberHomologyTransport_iff, ← fiberToPullback_comp_pullbackMapOfComp φ f p h₀,
    ← fiberToPullback_comp_pullbackMapOfComp φ f p h₁, Functor.map_comp, Functor.map_comp,
    fiberHomologyTransport_comp_map_assoc]

/-- **Naturality in maps of fibrations.** A commutative square `g ≫ p' = p ≫ c` of Serre fibrations
commutes with the transports through `K` along `f` and along `f ≫ c`, through the induced maps of
fibres `CategoryTheory.CommSq.fiberMap`. -/
theorem fiberHomologyTransport_comp_map_fiberMap {E' B' : TopCat.{u}} {p' : E' ⟶ B'}
    {g : E ⟶ E'} {c : B ⟶ B'} (hp' : serreFibrations p') (sq : CommSq g p p' c)
    (h₀ : f k₀ = b₀) (h₁ : f k₁ = b₁) :
    fiberHomologyTransport hp M n f h₀ h₁ ≫
        ((singularHomologyFunctor (ModuleCat.{u} R) n).obj M).map (sq.fiberMap b₁) =
      ((singularHomologyFunctor (ModuleCat.{u} R) n).obj M).map (sq.fiberMap b₀) ≫
        fiberHomologyTransport hp' M n (f ≫ c) (k₀ := k₀) (k₁ := k₁) (congrArg c h₀)
          (congrArg c h₁) := by
  have := isIso_singularHomologyMap_fiberToPullback hp' M n (f ≫ c) (k := k₁) (congrArg c h₁)
  rw [← cancel_mono (((singularHomologyFunctor (ModuleCat.{u} R) n).obj M).map
      (fiberToPullback (f ≫ c) p' (k := k₁) (congrArg c h₁))),
    Category.assoc, Category.assoc, fiberHomologyTransport_comp_map, ← Functor.map_comp,
    ← Functor.map_comp, ← sq.fiberToPullback_comp_pullbackMap f h₁,
    ← sq.fiberToPullback_comp_pullbackMap f h₀, Functor.map_comp, Functor.map_comp,
    fiberHomologyTransport_comp_map_assoc]

/-- **Naturality in the coefficients.** The transport through `K` commutes with the maps induced
by a linear map of coefficient modules. -/
theorem fiberHomologyTransport_comp_app {M' : ModuleCat.{u} R} (ψ : M ⟶ M') (h₀ : f k₀ = b₀)
    (h₁ : f k₁ = b₁) :
    fiberHomologyTransport hp M n f h₀ h₁ ≫
        ((singularHomologyFunctor (ModuleCat.{u} R) n).map ψ).app (p.fiber b₁) =
      ((singularHomologyFunctor (ModuleCat.{u} R) n).map ψ).app (p.fiber b₀) ≫
        fiberHomologyTransport hp M' n f h₀ h₁ := by
  have := isIso_singularHomologyMap_fiberToPullback hp M' n f h₁
  rw [← cancel_mono (((singularHomologyFunctor (ModuleCat.{u} R) n).obj M').map
      (fiberToPullback f p h₁)), Category.assoc, Category.assoc, fiberHomologyTransport_comp_map,
    ← NatTrans.naturality, fiberHomologyTransport_comp_map_assoc, NatTrans.naturality]

end Transport

/-! ### Transport along paths -/

/-- A path, as a morphism to `B` from the interval lifted to the universe of `B`. -/
private def pathULiftHom {b₀ b₁ : B} (γ : Path b₀ b₁) : _root_.TopCat.of (ULift.{u} I) ⟶ B :=
  _root_.TopCat.ofHom (γ.toContinuousMap.comp ⟨ULift.down, continuous_uliftDown⟩)

private lemma pathULiftHom_apply {b₀ b₁ : B} (γ : Path b₀ b₁) (t : ULift.{u} I) :
    pathULiftHom γ t = γ t.down :=
  (rfl)

/-- The first half `t ↦ t / 2` of the interval, parametrized by the interval. -/
private def halfLeft : _root_.TopCat.of (ULift.{u} I) ⟶ _root_.TopCat.of (ULift.{u} I) :=
  _root_.TopCat.ofHom ⟨fun t ↦ ULift.up ⟨(t.down : ℝ) / 2,
      div_nonneg t.down.2.1 zero_le_two, by linarith [t.down.2.2]⟩,
    continuous_uliftUp.comp (((continuous_subtype_val.comp continuous_uliftDown).div_const
      2).subtype_mk _)⟩

/-- The second half `t ↦ (1 + t) / 2` of the interval, parametrized by the interval. -/
private def halfRight : _root_.TopCat.of (ULift.{u} I) ⟶ _root_.TopCat.of (ULift.{u} I) :=
  _root_.TopCat.ofHom ⟨fun t ↦ ULift.up ⟨(1 + (t.down : ℝ)) / 2,
      by linarith [t.down.2.1], by linarith [t.down.2.2]⟩,
    continuous_uliftUp.comp (((continuous_const.add
      (continuous_subtype_val.comp continuous_uliftDown)).div_const 2).subtype_mk _)⟩

private lemma halfLeft_down (t : ULift.{u} I) : ((halfLeft t).down : ℝ) = t.down / 2 :=
  (rfl)

private lemma halfRight_down (t : ULift.{u} I) : ((halfRight t).down : ℝ) = (1 + t.down) / 2 :=
  (rfl)

/-- The first half of a concatenation of paths is the first path. -/
private lemma pathULiftHom_eq_halfLeft_comp {b₀ b₁ b₂ : B} (γ : Path b₀ b₁) (δ : Path b₁ b₂) :
    pathULiftHom γ = halfLeft ≫ pathULiftHom (γ.trans δ) := by
  ext t
  rw [ConcreteCategory.comp_apply, pathULiftHom_apply, pathULiftHom_apply, Path.trans_apply]
  split_ifs with h
  · -- The coordinate of the point `⟨2 * (t / 2), _⟩` is `2 * (t / 2)` by definition.
    exact congrArg γ (Subtype.ext (by ring : (t.down : ℝ) = 2 * ((t.down : ℝ) / 2)))
  · rw [halfLeft_down] at h
    linarith [t.down.2.2]

/-- The second half of a concatenation of paths is the second path. -/
private lemma pathULiftHom_eq_halfRight_comp {b₀ b₁ b₂ : B} (γ : Path b₀ b₁) (δ : Path b₁ b₂) :
    pathULiftHom δ = halfRight ≫ pathULiftHom (γ.trans δ) := by
  ext t
  rw [ConcreteCategory.comp_apply, pathULiftHom_apply, pathULiftHom_apply, Path.trans_apply]
  split_ifs with h
  · -- Only `t = 0` lands in the first half, at the junction point `δ 0 = γ 1`.
    rw [halfRight_down] at h
    have ht : (t.down : ℝ) = 0 := by linarith [t.down.2.1]
    calc δ t.down = δ 0 := congrArg δ (Subtype.ext ht)
      _ = γ 1 := δ.source.trans γ.target.symm
      _ = _ := congrArg γ (Subtype.ext
        (by rw [ht]; norm_num : ((1 : I) : ℝ) = 2 * ((1 + (t.down : ℝ)) / 2)))
  · exact congrArg δ (Subtype.ext (by ring : (t.down : ℝ) = 2 * ((1 + (t.down : ℝ)) / 2) - 1))

private theorem contractibleSpace_unitInterval : ContractibleSpace I :=
  (convex_Icc (0 : ℝ) 1).contractibleSpace ⟨0, by simp⟩

attribute [local instance] contractibleSpace_unitInterval

private theorem contractibleSpace_ulift_unitInterval :
    ContractibleSpace (_root_.TopCat.of (ULift.{u} I)) :=
  (Homeomorph.ulift : ULift.{u} I ≃ₜ I).contractibleSpace

private theorem contractibleSpace_ulift_unitInterval_prod :
    ContractibleSpace (_root_.TopCat.of (ULift.{u} (I × I))) :=
  (Homeomorph.ulift : ULift.{u} (I × I) ≃ₜ I × I).contractibleSpace

attribute [local instance] contractibleSpace_ulift_unitInterval
  contractibleSpace_ulift_unitInterval_prod

section Path

variable (hp : serreFibrations p) {R : Type v} [Ring R] (M : ModuleCat.{u} R) (n : ℕ)
  {b₀ b₁ b₂ : B}

/-- The **transport along a path** `γ` from `b₀` to `b₁` in the base of a Serre fibration: the
isomorphism `H_n(p⁻¹(b₀); M) → H_n(p⁻¹(b₁); M)` through the homology of the base change of `p`
along `γ`, the transport through the interval. -/
def serreTransport (γ : Path b₀ b₁) :
    ((singularHomologyFunctor (ModuleCat.{u} R) n).obj M).obj (p.fiber b₀) ⟶
      ((singularHomologyFunctor (ModuleCat.{u} R) n).obj M).obj (p.fiber b₁) :=
  fiberHomologyTransport hp M n (pathULiftHom γ) (k₀ := ULift.up 0) (k₁ := ULift.up 1) γ.source
    γ.target

instance isIso_serreTransport (γ : Path b₀ b₁) : IsIso (serreTransport hp M n γ) :=
  isIso_fiberHomologyTransport hp M n _ γ.source γ.target

/-- The transport along `γ` is the transport through `K` along `f`, whenever `γ` factors through
`f` by a map `φ` from the interval with `φ 0 = k₀` and `φ 1 = k₁`. -/
private theorem serreTransport_eq_of_eq_comp (γ : Path b₀ b₁) (f : K ⟶ B) [ContractibleSpace K]
    (φ : _root_.TopCat.of (ULift.{u} I) ⟶ K) (hγ : pathULiftHom γ = φ ≫ f) {k₀ k₁ : K}
    (e₀ : φ (ULift.up 0) = k₀) (e₁ : φ (ULift.up 1) = k₁) (h₀ : f k₀ = b₀) (h₁ : f k₁ = b₁) :
    serreTransport hp M n γ = fiberHomologyTransport hp M n f h₀ h₁ := by
  subst e₀ e₁
  have : serreTransport hp M n γ = fiberHomologyTransport hp M n (φ ≫ f) h₀ h₁ :=
    fiberHomologyTransport_congr hp M n hγ rfl rfl _ _ _ _
  rw [this, fiberHomologyTransport_comp_left]

/-- **Transport along the image of a path in a contractible space.** For `f : K ⟶ B` with `K`
contractible and a path `ε` from `k₀` to `k₁` in `K`, the transport along `f ∘ ε` is the transport
through `K` from `k₀` to `k₁`. -/
theorem serreTransport_map (f : K ⟶ B) [ContractibleSpace K] {k₀ k₁ : K} (ε : Path k₀ k₁) :
    serreTransport hp M n (ε.map f.hom.continuous) =
      fiberHomologyTransport hp M n f (rfl : f k₀ = f k₀) (rfl : f k₁ = f k₁) := by
  exact serreTransport_eq_of_eq_comp hp M n _ f
    (_root_.TopCat.ofHom (ε.toContinuousMap.comp ⟨ULift.down, continuous_uliftDown⟩)) rfl
    ε.source ε.target rfl rfl

/-- **Homotopy invariance of the transport.** Homotopic paths have the same transport. -/
theorem serreTransport_congr {γ γ' : Path b₀ b₁} (h : γ.Homotopic γ') :
    serreTransport hp M n γ = serreTransport hp M n γ' := by
  obtain ⟨F⟩ := h
  -- Parametrize the base change by the square `I × I` through the homotopy `F`; its sides
  -- `{0} × I` and `{1} × I` are `γ` and `γ'`.
  let f : _root_.TopCat.of (ULift.{u} (I × I)) ⟶ B :=
    _root_.TopCat.ofHom (F.toContinuousMap.comp ⟨ULift.down, continuous_uliftDown⟩)
  let φ (s : I) : _root_.TopCat.of (ULift.{u} I) ⟶ _root_.TopCat.of (ULift.{u} (I × I)) :=
    _root_.TopCat.ofHom ⟨fun t ↦ ULift.up (s, t.down), by fun_prop⟩
  have hγ : pathULiftHom γ = φ 0 ≫ f := by ext t; exact (F.apply_zero t.down).symm
  have hγ' : pathULiftHom γ' = φ 1 ≫ f := by ext t; exact (F.apply_one t.down).symm
  have h₀ : f (ULift.up (0, 0)) = b₀ := F.source 0
  have h₀' : f (ULift.up (1, 0)) = b₀ := F.source 1
  have h₁ : f (ULift.up (0, 1)) = b₁ := F.target 0
  have h₁' : f (ULift.up (1, 1)) = b₁ := F.target 1
  -- The sides `I × {0}` and `I × {1}` of the square lie in the fibres of `f` over `b₀` and `b₁`.
  let δ (t : I) : Path (ULift.up (0, t) : ULift.{u} (I × I)) (ULift.up (1, t)) :=
    ⟨⟨fun s ↦ ULift.up (s, t), by fun_prop⟩, rfl, rfl⟩
  have e₀ : fiberHomologyTransport hp M n f h₀ h₀' = 𝟙 _ :=
    fiberHomologyTransport_eq_id_of_path hp M n f (δ 0) (fun s ↦ F.source s) h₀ h₀'
  have e₁ : fiberHomologyTransport hp M n f h₁' h₁ = 𝟙 _ :=
    fiberHomologyTransport_eq_id_of_path hp M n f (δ 1).symm (fun s ↦ F.target _) h₁' h₁
  rw [serreTransport_eq_of_eq_comp hp M n γ f (φ 0) hγ rfl rfl h₀ h₁,
    serreTransport_eq_of_eq_comp hp M n γ' f (φ 1) hγ' rfl rfl h₀' h₁',
    ← fiberHomologyTransport_comp hp M n f h₀ h₀' h₁, e₀, Category.id_comp,
    ← fiberHomologyTransport_comp hp M n f h₀' h₁' h₁, e₁, Category.comp_id]

/-- Transport along a constant path is the identity. -/
@[simp]
theorem serreTransport_refl (b : B) : serreTransport hp M n (Path.refl b) = 𝟙 _ :=
  fiberHomologyTransport_eq_id_of_path hp M n (pathULiftHom (Path.refl b))
    ⟨⟨fun t ↦ ULift.up t, continuous_uliftUp⟩, rfl, rfl⟩ (fun _ ↦ rfl) _ _

/-- Transport along a concatenation of paths is the composite of the transports. -/
theorem serreTransport_trans (γ : Path b₀ b₁) (δ : Path b₁ b₂) :
    serreTransport hp M n (γ.trans δ) = serreTransport hp M n γ ≫ serreTransport hp M n δ := by
  have hm : pathULiftHom (γ.trans δ) (halfLeft (ULift.up 1)) = b₁ := by
    rw [← ConcreteCategory.comp_apply, ← pathULiftHom_eq_halfLeft_comp γ δ, pathULiftHom_apply,
      γ.target]
  rw [serreTransport_eq_of_eq_comp hp M n γ _ halfLeft (pathULiftHom_eq_halfLeft_comp γ δ)
      (ULift.ext (Subtype.ext (by rw [halfLeft_down]; simp; rfl))) rfl (γ.trans δ).source hm,
    serreTransport_eq_of_eq_comp hp M n δ _ halfRight (pathULiftHom_eq_halfRight_comp γ δ)
      (ULift.ext (Subtype.ext (by rw [halfLeft_down, halfRight_down]; simp)))
      (ULift.ext (Subtype.ext (by rw [halfRight_down]; norm_num; rfl))) hm (γ.trans δ).target]
  exact (fiberHomologyTransport_comp hp M n _ (γ.trans δ).source hm (γ.trans δ).target).symm

/-! ### The local system -/

/-- The **local system of fibre homology** `b ↦ H_n(p⁻¹(b); M)` of a Serre fibration `p`, with
singular homology with coefficients in a module `M`: a path acts by the transport along it. -/
def serreFiberLocalSystem : LocalCoefficientSystem.{v, u, u} R B where
  obj b := ((singularHomologyFunctor (ModuleCat.{u} R) n).obj M).obj (p.fiber b.as)
  map {b₀ b₁} := Quotient.lift (serreTransport hp M n) fun _ _ h ↦ serreTransport_congr hp M n h
  -- The identity of the fundamental groupoid is the class of the constant path
  -- (`FundamentalGroupoid.id_eq_path_refl`).
  map_id b := serreTransport_refl hp M n b.as
  -- Composition in the fundamental groupoid is the class of the concatenation
  -- (`FundamentalGroupoid.comp_eq`), on which `Quotient.lift` evaluates by definition.
  map_comp f g := by
    induction f using Path.Homotopic.Quotient.ind with | mk γ =>
    induction g using Path.Homotopic.Quotient.ind with | mk δ =>
    exact serreTransport_trans hp M n γ δ

/-- The value of the local system of fibre homology at a point is the homology of the fibre over
it. -/
def serreFiberLocalSystemObjIso (b : FundamentalGroupoid B) :
    (serreFiberLocalSystem hp M n).obj b ≅
      ((singularHomologyFunctor (ModuleCat.{u} R) n).obj M).obj (p.fiber b.as) :=
  Iso.refl _

/-- The local system sends the class of a path to the transport along it. -/
theorem serreFiberLocalSystem_map_mk {b₀ b₁ : FundamentalGroupoid B} (γ : Path b₀.as b₁.as) :
    (serreFiberLocalSystem hp M n).map (Path.Homotopic.Quotient.mk γ) =
      (serreFiberLocalSystemObjIso hp M n b₀).hom ≫ serreTransport hp M n γ ≫
        (serreFiberLocalSystemObjIso hp M n b₁).inv := by
  simp only [serreFiberLocalSystemObjIso, Iso.refl_hom, Iso.refl_inv]
  -- `Quotient.lift` evaluates on the class of a path by definition.
  rfl

/-- **Naturality of the transport in the coefficients.** -/
@[reassoc]
theorem serreTransport_comp_app {M' : ModuleCat.{u} R} (ψ : M ⟶ M') (γ : Path b₀ b₁) :
    serreTransport hp M n γ ≫
        ((singularHomologyFunctor (ModuleCat.{u} R) n).map ψ).app (p.fiber b₁) =
      ((singularHomologyFunctor (ModuleCat.{u} R) n).map ψ).app (p.fiber b₀) ≫
        serreTransport hp M' n γ :=
  fiberHomologyTransport_comp_app hp M n _ ψ _ _

/-- The morphism of local systems of fibre homology induced by a linear map of coefficient
modules: on each fibre, the map induced on homology by the coefficient map. -/
def serreFiberLocalSystemMapCoeff {M' : ModuleCat.{u} R} (ψ : M ⟶ M') :
    serreFiberLocalSystem hp M n ⟶ serreFiberLocalSystem hp M' n where
  app b := (serreFiberLocalSystemObjIso hp M n b).hom ≫
    ((singularHomologyFunctor (ModuleCat.{u} R) n).map ψ).app (p.fiber b.as) ≫
      (serreFiberLocalSystemObjIso hp M' n b).inv
  naturality {b₀ b₁} q := by
    induction q using Path.Homotopic.Quotient.ind with | mk γ =>
    simp only [serreFiberLocalSystem_map_mk, Category.assoc, Iso.inv_hom_id_assoc,
      serreTransport_comp_app_assoc]

theorem serreFiberLocalSystemMapCoeff_app {M' : ModuleCat.{u} R} (ψ : M ⟶ M')
    (b : FundamentalGroupoid B) :
    (serreFiberLocalSystemMapCoeff hp M n ψ).app b =
      (serreFiberLocalSystemObjIso hp M n b).hom ≫
        ((singularHomologyFunctor (ModuleCat.{u} R) n).map ψ).app (p.fiber b.as) ≫
          (serreFiberLocalSystemObjIso hp M' n b).inv :=
  (rfl)

/-- **Naturality of the transport in maps of fibrations.** A commutative square `g ≫ p' = p ≫ c`
of Serre fibrations commutes with the transports along `γ` and along its image under `c`, through
the induced maps of fibres `CategoryTheory.CommSq.fiberMap`. -/
@[reassoc]
theorem serreTransport_comp_map_fiberMap {E' B' : TopCat.{u}} {p' : E' ⟶ B'} {g : E ⟶ E'}
    {c : B ⟶ B'} (hp' : serreFibrations p') (sq : CommSq g p p' c) (γ : Path b₀ b₁) :
    serreTransport hp M n γ ≫
        ((singularHomologyFunctor (ModuleCat.{u} R) n).obj M).map (sq.fiberMap b₁) =
      ((singularHomologyFunctor (ModuleCat.{u} R) n).obj M).map (sq.fiberMap b₀) ≫
        serreTransport hp' M n (γ.map c.hom.continuous) := by
  exact fiberHomologyTransport_comp_map_fiberMap hp M n (pathULiftHom γ) hp' sq γ.source
    γ.target

/-! ### Comparison with Hurewicz fibrations -/

/-- **Transport in a Hurewicz fibration.** If `p` has a lifting function `Λ`, the transport along
a path `γ` is the map induced on homology by the transport `Λ.transport γ` of the points of the
fibre along the lifts of `γ`. -/
theorem serreTransport_eq_map_transport (Λ : LiftingFunction p.hom) (γ : Path b₀ b₁) :
    serreTransport hp M n γ =
      ((singularHomologyFunctor (ModuleCat.{u} R) n).obj M).map
        (_root_.TopCat.ofHom (Λ.transport γ)) := by
  refine ((eq_fiberHomologyTransport_iff hp M n (pathULiftHom γ) γ.source γ.target _).2 ?_).symm
  rw [← Functor.map_comp]
  -- The fibre inclusion at the end of `γ`, after the transport, is homotopic to the fibre
  -- inclusion at the start, through the lifts of `γ`.
  let H : _root_.TopCat.Homotopy (fiberToPullback (pathULiftHom γ) p γ.source)
      (_root_.TopCat.ofHom (Λ.transport γ) ≫ fiberToPullback (pathULiftHom γ) p γ.target) :=
    { toFun z := ⟨(ULift.up z.1,
          Λ.lift z.2.1 γ.toContinuousMap (γ.source.trans (z.2.2 : p z.2.1 = b₀).symm) z.1),
        (Λ.apply_lift _ _ _ _).symm⟩
      continuous_toFun := by
        refine Continuous.subtype_mk ((continuous_uliftUp.comp continuous_fst).prodMk ?_) _
        exact continuous_eval.comp
          ((Λ.continuous_lift (continuous_subtype_val.comp continuous_snd) continuous_const
            _).prodMk continuous_fst)
      -- The first components agree by definition of `fiberToPullback`.
      map_zero_left x := Subtype.ext (Prod.ext rfl (Λ.lift_zero _ _ _))
      map_one_left x := Subtype.ext (Prod.ext rfl (Λ.transport_apply_coe γ x).symm) }
  exact (TopCat.Homotopy.congr_homologyMap_singularChainComplexFunctor H M n).symm

end Path

end TauCeti.TopCat

/-! ### Naturality in maps of fibrations -/

namespace CategoryTheory.CommSq

open TauCeti.TopCat

variable {E B E' B' : TopCat.{u}} {p : E ⟶ B} {p' : E' ⟶ B'} {g : E ⟶ E'} {c : B ⟶ B'}
  {R : Type v} [Ring R]

/-- **Functoriality of the local system of fibre homology in maps of Serre fibrations.** A
commutative square `g ≫ p' = p ≫ c` maps the local system of fibre homology of `p` to the pullback
along `c` of that of `p'`, acting on each fibre by the map induced by `CommSq.fiberMap`. -/
def serreFiberLocalSystemMap (sq : CommSq g p p' c) (hp : serreFibrations p)
    (hp' : serreFibrations p') (M : ModuleCat.{u} R) (n : ℕ) :
    serreFiberLocalSystem hp M n ⟶
      (TauCeti.LocalCoefficientSystem.pullback c.hom).obj (serreFiberLocalSystem hp' M n) where
  app b := (serreFiberLocalSystemObjIso hp M n b).hom ≫
    ((singularHomologyFunctor (ModuleCat.{u} R) n).obj M).map (sq.fiberMap b.as) ≫
      (serreFiberLocalSystemObjIso hp' M n (.mk (c b.as))).inv
  naturality {b₀ b₁} q := by
    induction q using Path.Homotopic.Quotient.ind with | mk γ =>
    -- The pulled-back functor agrees with `serreFiberLocalSystem hp' M n` on `.mk (c b.as)` only
    -- up to unfolding `FundamentalGroupoid.map`, so `change` aligns the endpoints before `rw`.
    change (serreFiberLocalSystem hp M n).map (Path.Homotopic.Quotient.mk γ) ≫
        ((serreFiberLocalSystemObjIso hp M n b₁).hom ≫
          ((singularHomologyFunctor (ModuleCat.{u} R) n).obj M).map (sq.fiberMap b₁.as) ≫
          (serreFiberLocalSystemObjIso hp' M n (.mk (c b₁.as))).inv) =
      ((serreFiberLocalSystemObjIso hp M n b₀).hom ≫
          ((singularHomologyFunctor (ModuleCat.{u} R) n).obj M).map (sq.fiberMap b₀.as) ≫
          (serreFiberLocalSystemObjIso hp' M n (.mk (c b₀.as))).inv) ≫
        (serreFiberLocalSystem hp' M n).map (Path.Homotopic.Quotient.mk (γ.map c.hom.continuous))
    rw [serreFiberLocalSystem_map_mk, serreFiberLocalSystem_map_mk]
    simp only [Category.assoc, Iso.inv_hom_id_assoc,
      serreTransport_comp_map_fiberMap_assoc hp M n hp' sq γ]
    rfl

theorem serreFiberLocalSystemMap_app (sq : CommSq g p p' c) (hp : serreFibrations p)
    (hp' : serreFibrations p') (M : ModuleCat.{u} R) (n : ℕ) (b : FundamentalGroupoid B) :
    (sq.serreFiberLocalSystemMap hp hp' M n).app b =
      (serreFiberLocalSystemObjIso hp M n b).hom ≫
        ((singularHomologyFunctor (ModuleCat.{u} R) n).obj M).map (sq.fiberMap b.as) ≫
        (serreFiberLocalSystemObjIso hp' M n (.mk (c b.as))).inv :=
  (rfl)

end CategoryTheory.CommSq
