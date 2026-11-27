/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.FiberBundle.Principal.Basic
public import TauCeti.Topology.FiberBundle.Principal.Equiv
public import TauCeti.Topology.VectorBundle.OrthonormalFrame.Isometry

/-!
# Lifts of orthonormal frame bundles along a structure group homomorphism

Let `E → X` be a real vector bundle with model fibre `F` and fibre inner products, let `G` be a
group with a topology and let `ρ : G →* GL(ℝⁿ)` be a homomorphism, written as a homomorphism into
the linear automorphisms of `Fin n → ℝ`. A *lift of the orthonormal frame bundle of `E` along `ρ`*
(`TauCeti.OrthonormalFrameLift`) is a principal `G`-bundle `P → X` together with a continuous map
`P → Fr(E)` to the orthonormal frame bundle of `E` modelled on `ℝⁿ`, covering the identity of `X`
and equivariant along `ρ`: the frame of `p • g` sends `v` to the frame of `p` applied to `ρ g v`.

For `ρ` the vector action `Spin(n) → SO(n)` this is a Spin structure, and for the rotation
homomorphism `[s, z] ↦ π(s)` of `Spinᶜ(n)` a `Spinᶜ` structure (both in
`TauCeti.Topology.VectorBundle.SpinStructure.Basic`); other choices of `ρ` give other reductions
and lifts of the structure group. Only the frame map and its equivariance are recorded: when `ρ`
lands in `SO(n)`, each fibre of `P` is a `G`-torsor, so its image is one `ρG`-orbit of frames,
contained in one `SO(n)`-orbit, which singles out an orientation of `E`. There is no numerability
field; on paracompact Hausdorff bases every principal bundle is numerable.

An *equivalence* of lifts (`TauCeti.OrthonormalFrameLift.Equiv`) is an equivalence of the two
principal bundles (`TauCeti.PrincipalBundle.Equiv`), a family of equivariant bijections between
their fibres, inducing a homeomorphism of total
spaces (`TauCeti.OrthonormalFrameLift.Equiv.toHomeomorph`) and commuting with the frame maps.
Equivalences have identities, inverses and composites.

The *pullback* of a lift along a continuous map `f : Y → X`
(`TauCeti.OrthonormalFrameLift.pullback`) is the pulled-back principal bundle `f *ᵖ P` with the
frame map read through the identification of the frames of `f *ᵖ E` at `y` with the frames of `E`
at `f y` (`TauCeti.OrthonormalFrameBundle.pullbackHomeomorph`). Equivalences pull back to
equivalences (`TauCeti.OrthonormalFrameLift.Equiv.pullback`).

Lifts are natural under bundle isometries. The *transport* of a lift along a family of fibrewise
linear isometric equivalences `Φ x : E x ≃ₗᵢ[ℝ] E' x`, continuous as a map of total spaces
(`TauCeti.OrthonormalFrameLift.map`), keeps the principal bundle and composes the frame map with
the induced map of orthonormal frame bundles (`TauCeti.OrthonormalFrameBundle.map`). Transport is
functorial in `Φ`, for lifts and for their equivalences (`TauCeti.OrthonormalFrameLift.map_refl`,
`TauCeti.OrthonormalFrameLift.map_map`, `TauCeti.OrthonormalFrameLift.Equiv.map_refl_heq`,
`TauCeti.OrthonormalFrameLift.Equiv.map_map_heq`), commutes with pullback
(`TauCeti.OrthonormalFrameLift.pullback_map`), and is injective on lifts
(`TauCeti.OrthonormalFrameLift.map_injective`); when the inverse isometries are continuous too it
is a bijection from the lifts for `E` to the lifts for `E'`
(`TauCeti.OrthonormalFrameLift.map_surjective`). It identifies the equivalences of two lifts with
those of their transports (`TauCeti.OrthonormalFrameLift.equivMapEquiv`). A change of metric is the
main instance.

Precomposing every frame of a lift along `ρ` with a fixed linear isometry `r` of the model gives
a lift along any `ρ'` with `ρ g ∘ r = r ∘ ρ' g`, on the same principal bundle
(`TauCeti.OrthonormalFrameLift.precomp`). Equivalences of lifts are equivalences of the lifts with
precomposed frames (`TauCeti.OrthonormalFrameLift.Equiv.precomp`).

## Main definitions

* `TauCeti.OrthonormalFrameLift`: a lift of the orthonormal frame bundle of a real vector bundle
  with fibre inner products along a homomorphism `ρ : G →* GL(ℝⁿ)`.
* `TauCeti.OrthonormalFrameLift.frameAt`: the orthonormal frame of `E x` at a point of `P`.
* `TauCeti.OrthonormalFrameLift.Equiv`: equivalences of lifts, with `refl`, `symm`, `trans`.
* `TauCeti.OrthonormalFrameLift.pullback`: the pullback of a lift along a continuous map.
* `TauCeti.OrthonormalFrameLift.Equiv.pullback`: the pullback of an equivalence.
* `TauCeti.OrthonormalFrameLift.map`, `TauCeti.OrthonormalFrameLift.Equiv.map`: the transport of a
  lift and of an equivalence along fibrewise isometries.
* `TauCeti.OrthonormalFrameLift.precomp`: the lift whose frames are those of a lift precomposed
  with a fixed isometry of the model.
* `TauCeti.OrthonormalFrameLift.Equiv.precomp`: the equivalence of lifts with precomposed frames
  induced by an equivalence of lifts.

## Main results

* `TauCeti.OrthonormalFrameLift.frameAt_smul`: the frame of `p • g` is the frame of `p`
  precomposed with `ρ g`.
* `TauCeti.OrthonormalFrameLift.finrank_fiber`, `TauCeti.OrthonormalFrameLift.finrank_model`:
  a bundle whose orthonormal frame bundle of rank `n` has a lift has fibres of dimension `n`.
* `TauCeti.OrthonormalFrameLift.pullback_map`,
  `TauCeti.OrthonormalFrameLift.Equiv.pullback_map_heq`: transport of lifts and of equivalences
  commutes with pullback.
* `TauCeti.OrthonormalFrameLift.nonempty_equiv_map_iff`: transport preserves and reflects
  equivalence of lifts.

## References

* S. Kobayashi, K. Nomizu, *Foundations of Differential Geometry*, Vol. I, Interscience, 1963,
  Chapter I, §5 (reductions of the structure group).
* H. B. Lawson, M.-L. Michelsohn, *Spin Geometry*, Princeton University Press, 1989, Chapter II,
  §1 and Appendix D.
-/

public section

open Bundle MulOpposite

universe w

namespace TauCeti

/-- A **lift of the orthonormal frame bundle** of a real vector bundle `E` with model fibre `F` and
fibre inner products along a homomorphism `ρ : G →* GL(ℝⁿ)`: a principal `G`-bundle `P` over the
base, together with a continuous map to the orthonormal frame bundle of `E` modelled on `ℝⁿ` over
the identity, equivariant along `ρ`: the frame of `p • g` sends `v` to the frame of `p` applied to
`ρ g v`. For `ρ` the vector action of `Spin(n)` this is a Spin structure, and for the rotation
homomorphism of `Spinᶜ(n)` a `Spinᶜ` structure. -/
structure OrthonormalFrameLift {X : Type*} [TopologicalSpace X] (F : Type*) (E : X → Type w)
    [TopologicalSpace (TotalSpace F E)]
    [∀ x, NormedAddCommGroup (E x)] [∀ x, InnerProductSpace ℝ (E x)] (n : ℕ)
    (G : Type*) [Group G] [TopologicalSpace G] (ρ : G →* (Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ)) where
  /-- The fibres of the principal `G`-bundle. -/
  P : X → Type w
  /-- The topology of the total space of `P`. -/
  [topTotal : TopologicalSpace (TotalSpace G P)]
  /-- The topologies of the fibres of `P`. -/
  [topFiber : ∀ x, TopologicalSpace (P x)]
  /-- The right action of `G` on the fibres of `P`. -/
  [act : ∀ x, MulAction Gᵐᵒᵖ (P x)]
  /-- `P` is a fibre bundle with model fibre `G`. -/
  [fiberBundle : FiberBundle G P]
  /-- The trivializations of the atlas of `P` are equivariant. -/
  [principal : PrincipalBundle G P]
  /-- The map to the orthonormal frames of `E`. -/
  toFrame : TotalSpace G P → OrthonormalFrameBundle ℝ F E (EuclideanSpace ℝ (Fin n))
  /-- The map to frames is continuous. -/
  continuous_toFrame : Continuous toFrame
  /-- The map to frames covers the identity of the base. -/
  proj_toFrame : ∀ p, (toFrame p).proj = p.proj
  /-- The map to frames is equivariant along `ρ`. -/
  toFrame_smul : ∀ (x : X) (p : P x) (g : G) (v : Fin n → ℝ),
    TotalSpace.mk' F (toFrame ⟨x, op g • p⟩).proj
        ((toFrame ⟨x, op g • p⟩).frame (WithLp.toLp 2 v)) =
      TotalSpace.mk' F (toFrame ⟨x, p⟩).proj
        ((toFrame ⟨x, p⟩).frame (WithLp.toLp 2 (ρ g v)))

namespace OrthonormalFrameLift

attribute [instance] topTotal topFiber act fiberBundle principal

attribute [simp] proj_toFrame

variable {X : Type*} [TopologicalSpace X] {F : Type*} {E : X → Type w}
  [TopologicalSpace (TotalSpace F E)]
  [∀ x, NormedAddCommGroup (E x)] [∀ x, InnerProductSpace ℝ (E x)] {n : ℕ}
  {G : Type*} [Group G] [TopologicalSpace G] {ρ : G →* (Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ)}

/-- The fibres of the principal bundle of a lift are nonempty: each is homeomorphic to `G`. -/
instance nonempty_P (s : OrthonormalFrameLift F E n G ρ) (x : X) : Nonempty (s.P x) :=
  ⟨(FiberBundle.homeomorphAt G s.P x).symm 1⟩

/-- The orthonormal frame attached to a point `p` of `P` equals `⟨p.proj, φ⟩` for some
orthonormal frame `φ : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] E p.proj`. -/
theorem exists_toFrame_eq_mk (s : OrthonormalFrameLift F E n G ρ) (p : TotalSpace G s.P) :
    ∃ φ : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] E p.proj, s.toFrame p = ⟨p.proj, φ⟩ :=
  ⟨s.proj_toFrame p ▸ (s.toFrame p).frame,
    OrthonormalFrameBundle.eq_mk_of_proj_eq (s.toFrame p) (s.proj_toFrame p)⟩

/-- The orthonormal frame `ℝⁿ ≃ E x` attached to a point `p` of the fibre of `P` over `x`: the frame
of `s.toFrame ⟨x, p⟩`, read as a frame of `E x` (`TauCeti.OrthonormalFrameLift.toFrame_mk`). -/
noncomputable def frameAt (s : OrthonormalFrameLift F E n G ρ) {x : X} (p : s.P x) :
    EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] E x :=
  (s.exists_toFrame_eq_mk ⟨x, p⟩).choose

/-- The frame map at `⟨x, p⟩` is the frame `s.frameAt p` over `x`. -/
theorem toFrame_mk (s : OrthonormalFrameLift F E n G ρ) {x : X} (p : s.P x) :
    s.toFrame ⟨x, p⟩ = ⟨x, s.frameAt p⟩ :=
  (s.exists_toFrame_eq_mk ⟨x, p⟩).choose_spec

/-- **Equivariance of the frames**: the frame of `p • g` sends `v` to the frame of `p` applied to
`ρ g v`. -/
theorem frameAt_smul (s : OrthonormalFrameLift F E n G ρ) {x : X} (p : s.P x) (g : G)
    (v : Fin n → ℝ) :
    s.frameAt (op g • p) (WithLp.toLp 2 v) = s.frameAt p (WithLp.toLp 2 (ρ g v)) := by
  have h := s.toFrame_smul x p g v
  rw [toFrame_mk, toFrame_mk] at h
  exact TotalSpace.mk_inj.1 h

/-- Every fibre `E x` of a bundle whose orthonormal frame bundle of rank `n` has a lift is
finite-dimensional. -/
theorem finiteDimensional_fiber (s : OrthonormalFrameLift F E n G ρ) (x : X) :
    FiniteDimensional ℝ (E x) := by
  obtain ⟨p⟩ := s.nonempty_P x
  obtain ⟨φ, -⟩ := s.exists_toFrame_eq_mk ⟨x, p⟩
  exact φ.toLinearEquiv.finiteDimensional

/-- Every fibre `E x` of a bundle whose orthonormal frame bundle of rank `n` has a lift has
dimension `n`. -/
theorem finrank_fiber (s : OrthonormalFrameLift F E n G ρ) (x : X) :
    Module.finrank ℝ (E x) = n := by
  obtain ⟨p⟩ := s.nonempty_P x
  obtain ⟨φ, -⟩ := s.exists_toFrame_eq_mk ⟨x, p⟩
  simpa [finrank_euclideanSpace_fin] using φ.toLinearEquiv.finrank_eq.symm

/-- Over a nonempty base, the model fibre `F` of a vector bundle whose orthonormal frame bundle of
rank `n` has a lift is finite-dimensional. -/
theorem finiteDimensional_model [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiberBundle F E] [VectorBundle ℝ F E] [Nonempty X] (s : OrthonormalFrameLift F E n G ρ) :
    FiniteDimensional ℝ F := by
  obtain ⟨x⟩ := ‹Nonempty X›
  have := s.finiteDimensional_fiber x
  exact ((trivializationAt F E x).linearEquivAt ℝ x
    (FiberBundle.mem_baseSet_trivializationAt' x)).finiteDimensional

/-- Over a nonempty base, the model fibre `F` of a vector bundle whose orthonormal frame bundle of
rank `n` has a lift has dimension `n`. -/
theorem finrank_model [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiberBundle F E] [VectorBundle ℝ F E] [Nonempty X] (s : OrthonormalFrameLift F E n G ρ) :
    Module.finrank ℝ F = n := by
  obtain ⟨x⟩ := ‹Nonempty X›
  rw [← ((trivializationAt F E x).linearEquivAt ℝ x
    (FiberBundle.mem_baseSet_trivializationAt' x)).finrank_eq, s.finrank_fiber x]

/-- Elements of the kernel of `ρ` act trivially on frames: if `ρ g = 1`, the frame of `p • g` is
the frame of `p`. -/
theorem toFrame_smul_of_map_eq_one (s : OrthonormalFrameLift F E n G ρ) {g : G} (hg : ρ g = 1)
    (x : X) (p : s.P x) : s.toFrame ⟨x, op g • p⟩ = s.toFrame ⟨x, p⟩ :=
  OrthonormalFrameBundle.ext_totalSpaceMk fun v ↦ by
    rw [s.toFrame_smul, hg, FunLike.coe_one_eq_id, id_eq]

/-! ### Equivalences -/

/-- An **equivalence of lifts** `s ≃ t` on the same bundle: an equivalence of their principal
`G`-bundles (`TauCeti.PrincipalBundle.Equiv`), that is a family of bijections between the fibres,
equivariant for the right action of `G` and inducing continuous maps of total spaces in both
directions, commuting with the maps to the orthonormal frame bundle. -/
structure Equiv (s t : OrthonormalFrameLift F E n G ρ) extends
    toPrincipalBundleEquiv : PrincipalBundle.Equiv G s.P t.P where
  /-- The bijection commutes with the maps to frames. -/
  toFrame_map : ∀ (x : X) (p : s.P x), t.toFrame ⟨x, toEquiv x p⟩ = s.toFrame ⟨x, p⟩

namespace Equiv

variable {s t u : OrthonormalFrameLift F E n G ρ}

attribute [simp] toFrame_map

/-- The inverse of the bijection of an equivalence commutes with the maps to frames. -/
@[simp]
theorem toFrame_map_symm (φ : s.Equiv t) (x : X) (p : t.P x) :
    s.toFrame ⟨x, (φ.toEquiv x).symm p⟩ = t.toFrame ⟨x, p⟩ := by
  rw [← φ.toFrame_map x ((φ.toEquiv x).symm p), _root_.Equiv.apply_symm_apply]

/-- Two equivalences of lifts are equal when their bijections agree pointwise. -/
@[ext]
theorem ext {φ ψ : s.Equiv t} (h : ∀ x p, φ.toEquiv x p = ψ.toEquiv x p) : φ = ψ := by
  obtain ⟨φ, _⟩ := φ
  obtain ⟨ψ, _⟩ := ψ
  congr
  exact PrincipalBundle.Equiv.ext h

/-- Equivalences between equal lifts are heterogeneously equal when their bijections are,
fibre by fibre. This compares equivalences whose source and target lifts agree only
propositionally. -/
theorem heq_of_toEquiv_heq {s' t' : OrthonormalFrameLift F E n G ρ} (hs : s = s') (ht : t = t')
    {φ : s.Equiv t} {ψ : s'.Equiv t'} (h : ∀ x, HEq (φ.toEquiv x) (ψ.toEquiv x)) : HEq φ ψ := by
  subst hs ht
  exact heq_of_eq (ext fun x p ↦ congrFun (congrArg DFunLike.coe (eq_of_heq (h x))) p)

/-- The homeomorphism of total spaces induced by an equivalence of lifts. -/
def toHomeomorph (φ : s.Equiv t) :
    TotalSpace G s.P ≃ₜ TotalSpace G t.P
    where
  toFun p := ⟨p.proj, φ.toEquiv p.proj p.snd⟩
  invFun p := ⟨p.proj, (φ.toEquiv p.proj).symm p.snd⟩
  left_inv p := by simp
  right_inv p := by simp
  continuous_toFun := φ.continuous_toFun
  continuous_invFun := φ.continuous_invFun

@[simp]
theorem toHomeomorph_apply (φ : s.Equiv t) (p : TotalSpace G s.P) :
    φ.toHomeomorph p = ⟨p.proj, φ.toEquiv p.proj p.snd⟩ :=
  (rfl)

@[simp]
theorem toHomeomorph_symm_apply (φ : s.Equiv t)
    (p : TotalSpace G t.P) :
    φ.toHomeomorph.symm p = ⟨p.proj, (φ.toEquiv p.proj).symm p.snd⟩ :=
  (rfl)

/-- The homeomorphism of total spaces induced by an equivalence covers the identity of the
base. -/
theorem proj_toHomeomorph (φ : s.Equiv t) (p : TotalSpace G s.P) :
    (φ.toHomeomorph p).proj = p.proj :=
  (rfl)

/-- The homeomorphism of total spaces induced by an equivalence commutes with the maps to
frames. -/
theorem toFrame_toHomeomorph (φ : s.Equiv t) (p : TotalSpace G s.P) :
    t.toFrame (φ.toHomeomorph p) = s.toFrame p :=
  φ.toFrame_map p.proj p.snd

/-- The homeomorphism of total spaces induced by an equivalence is equivariant. -/
theorem toHomeomorph_smul (φ : s.Equiv t) (g : Gᵐᵒᵖ)
    (p : TotalSpace G s.P) :
    φ.toHomeomorph (g • p) = g • φ.toHomeomorph p :=
  congrArg (TotalSpace.mk p.proj) (φ.map_smul p.proj p.snd g.unop)

/-- The inverse homeomorphism of total spaces induced by an equivalence covers the identity of the
base. -/
theorem proj_toHomeomorph_symm (φ : s.Equiv t) (p : TotalSpace G t.P) :
    (φ.toHomeomorph.symm p).proj = p.proj :=
  (rfl)

/-- The inverse homeomorphism of total spaces induced by an equivalence commutes with the maps to
frames. -/
theorem toFrame_toHomeomorph_symm (φ : s.Equiv t)
    (p : TotalSpace G t.P) :
    s.toFrame (φ.toHomeomorph.symm p) = t.toFrame p :=
  φ.toFrame_map_symm p.proj p.snd

/-- The inverse homeomorphism of total spaces induced by an equivalence is equivariant. -/
theorem toHomeomorph_symm_smul (φ : s.Equiv t) (g : Gᵐᵒᵖ)
    (p : TotalSpace G t.P) :
    φ.toHomeomorph.symm (g • p) = g • φ.toHomeomorph.symm p :=
  congrArg (TotalSpace.mk p.proj) (φ.map_smul_symm p.proj p.snd g.unop)

/-- The identity equivalence of a lift. -/
@[refl]
def refl (s : OrthonormalFrameLift F E n G ρ) : s.Equiv s where
  toPrincipalBundleEquiv := .refl G s.P
  toFrame_map _ _ := rfl

/-- The inverse of an equivalence of lifts. -/
@[symm]
def symm (φ : s.Equiv t) : t.Equiv s where
  toPrincipalBundleEquiv := φ.toPrincipalBundleEquiv.symm
  toFrame_map := φ.toFrame_map_symm

/-- The composite of two equivalences of lifts. -/
@[trans]
def trans (φ : s.Equiv t) (ψ : t.Equiv u) : s.Equiv u where
  toPrincipalBundleEquiv := φ.toPrincipalBundleEquiv.trans ψ.toPrincipalBundleEquiv
  toFrame_map x p := by
    simp only [PrincipalBundle.Equiv.trans_toEquiv, _root_.Equiv.trans_apply, ψ.toFrame_map,
      φ.toFrame_map]

@[simp]
theorem refl_toEquiv (s : OrthonormalFrameLift F E n G ρ) (x : X) :
    (refl s).toEquiv x = _root_.Equiv.refl (s.P x) :=
  (rfl)

@[simp]
theorem symm_toEquiv (φ : s.Equiv t) (x : X) : φ.symm.toEquiv x = (φ.toEquiv x).symm :=
  (rfl)

@[simp]
theorem trans_toEquiv (φ : s.Equiv t) (ψ : t.Equiv u) (x : X) :
    (φ.trans ψ).toEquiv x = (φ.toEquiv x).trans (ψ.toEquiv x) :=
  (rfl)

/-- If `φ` sends `z` to `w` and `ψ` sends `w` to `r`, then `φ.trans ψ` sends `z` to `r`. The values
are taken as hypotheses, so that they can be supplied when the fibres are only definitionally equal
to the expected ones, where `rw` cannot rewrite. -/
theorem trans_toEquiv_apply_of_eq (φ : s.Equiv t) (ψ : t.Equiv u) {x : X} {z : s.P x}
    {w : t.P x} {r : u.P x} (hz : φ.toEquiv x z = w) (hw : ψ.toEquiv x w = r) :
    (φ.trans ψ).toEquiv x z = r := by
  rw [trans_toEquiv, _root_.Equiv.trans_apply, hz, hw]

/-- If `φ` sends `w` to `z`, then `φ.symm` sends `z` to `w`. -/
theorem symm_toEquiv_apply_of_eq (φ : s.Equiv t) {x : X} {z : t.P x} {w : s.P x}
    (h : φ.toEquiv x w = z) : φ.symm.toEquiv x z = w := by
  rw [symm_toEquiv, _root_.Equiv.symm_apply_eq, h]

@[simp]
theorem symm_symm (φ : s.Equiv t) : φ.symm.symm = φ :=
  (rfl)

@[simp]
theorem refl_symm (s : OrthonormalFrameLift F E n G ρ) : (refl s).symm = refl s :=
  (rfl)

@[simp]
theorem refl_trans (φ : s.Equiv t) : (refl s).trans φ = φ :=
  (rfl)

@[simp]
theorem trans_refl (φ : s.Equiv t) : φ.trans (refl t) = φ :=
  (rfl)

@[simp]
theorem self_trans_symm (φ : s.Equiv t) : φ.trans φ.symm = refl s :=
  ext fun x p ↦ (φ.toEquiv x).symm_apply_apply p

@[simp]
theorem symm_trans_self (φ : s.Equiv t) : φ.symm.trans φ = refl t :=
  ext fun x p ↦ (φ.toEquiv x).apply_symm_apply p

@[simp]
theorem symm_trans (φ : s.Equiv t) (ψ : t.Equiv u) : (φ.trans ψ).symm = ψ.symm.trans φ.symm :=
  (rfl)

@[simp]
theorem refl_toHomeomorph (s : OrthonormalFrameLift F E n G ρ) :
    (refl s).toHomeomorph = Homeomorph.refl _ :=
  (rfl)

@[simp]
theorem symm_toHomeomorph (φ : s.Equiv t) : φ.symm.toHomeomorph = φ.toHomeomorph.symm :=
  (rfl)

@[simp]
theorem trans_toHomeomorph (φ : s.Equiv t) (ψ : t.Equiv u) :
    (φ.trans ψ).toHomeomorph = φ.toHomeomorph.trans ψ.toHomeomorph :=
  (rfl)

theorem trans_assoc (φ : s.Equiv t) (ψ : t.Equiv u) {v : OrthonormalFrameLift F E n G ρ}
    (χ : u.Equiv v) : (φ.trans ψ).trans χ = φ.trans (ψ.trans χ) :=
  (rfl)

end Equiv

/-! ### Pullback -/

section Pullback

variable {Y : Type*} [TopologicalSpace Y] {K : Type*} [FunLike K Y X] [ContinuousMapClass K Y X]

/-- The map to frames of the pullback of a lift: the frame of `E` at `f y` of the
underlying point of `P`, read as a frame of `f *ᵖ E` at `y`. -/
noncomputable def pullbackToFrame (s : OrthonormalFrameLift F E n G ρ) (f : Y → X)
    (p : TotalSpace G (f *ᵖ s.P)) :
    OrthonormalFrameBundle ℝ F (f *ᵖ E) (EuclideanSpace ℝ (Fin n)) :=
  (OrthonormalFrameBundle.pullbackHomeomorph f).symm
    ⟨(p.proj, s.toFrame (Pullback.lift f p)), s.proj_toFrame _⟩

@[simp]
theorem proj_pullbackToFrame (s : OrthonormalFrameLift F E n G ρ) (f : Y → X)
    (p : TotalSpace G (f *ᵖ s.P)) :
    (s.pullbackToFrame f p).proj = p.proj :=
  OrthonormalFrameBundle.proj_pullbackHomeomorph_symm f _

/-- The frame of a point of the pullback, viewed as a frame of `E`, is the frame of the underlying
point of `P`. -/
@[simp]
theorem pullbackLift_pullbackToFrame (s : OrthonormalFrameLift F E n G ρ) (f : Y → X)
    (p : TotalSpace G (f *ᵖ s.P)) :
    OrthonormalFrameBundle.pullbackLift f (s.pullbackToFrame f p) =
      s.toFrame (Pullback.lift f p) :=
  OrthonormalFrameBundle.pullbackLift_pullbackHomeomorph_symm f _

/-- The map to frames of the pullback of a lift is continuous. -/
theorem continuous_pullbackToFrame (s : OrthonormalFrameLift F E n G ρ) (f : Y → X) :
    Continuous (s.pullbackToFrame f) :=
  (OrthonormalFrameBundle.pullbackHomeomorph f).continuous_symm.comp
    (((Pullback.continuous_proj _ _ _).prodMk
      (s.continuous_toFrame.comp (Pullback.continuous_lift _ _ _))).subtype_mk _)

/-- The **pullback of a lift** along a continuous map `f : Y → X`: the pulled-back
principal bundle `f *ᵖ P`, with the frame of a point over `y` the frame of `E` at `f y` of the
underlying point of `P`, read as a frame of `f *ᵖ E` at `y`. Its body is exposed so that the
fibre `(s.pullback f).P y` unfolds to `s.P (f y)` downstream. -/
@[expose]
noncomputable def pullback (s : OrthonormalFrameLift F E n G ρ) (f : K) :
    OrthonormalFrameLift F ((f : Y → X) *ᵖ E) n G ρ where
  P := (f : Y → X) *ᵖ s.P
  toFrame := s.pullbackToFrame f
  continuous_toFrame := s.continuous_pullbackToFrame f
  proj_toFrame := s.proj_pullbackToFrame f
  toFrame_smul y p g v := by
    refine Pullback.totalSpace_ext ((s.proj_pullbackToFrame f ⟨y, op g • p⟩).trans
      (s.proj_pullbackToFrame f ⟨y, p⟩).symm) ?_
    have h := s.toFrame_smul (f y) p g v
    simp only [TotalSpace.mk'] at h ⊢
    rw [← OrthonormalFrameBundle.totalSpaceMk_pullbackLift_frame,
      ← OrthonormalFrameBundle.totalSpaceMk_pullbackLift_frame,
      pullbackLift_pullbackToFrame, pullbackLift_pullbackToFrame]
    exact h

@[simp]
theorem pullback_P (s : OrthonormalFrameLift F E n G ρ) (f : K) :
    (s.pullback f).P = (f : Y → X) *ᵖ s.P :=
  rfl

theorem pullback_toFrame (s : OrthonormalFrameLift F E n G ρ) (f : K) :
    (s.pullback f).toFrame = s.pullbackToFrame f :=
  rfl

/-- The frame of a point of the pullback of a lift, viewed as a frame of `E`, is the frame of the
underlying point of `P`. -/
@[simp]
theorem pullbackLift_toFrame_pullback (s : OrthonormalFrameLift F E n G ρ) (f : K)
    (p : TotalSpace G (s.pullback f).P) :
    OrthonormalFrameBundle.pullbackLift f ((s.pullback f).toFrame p) =
      s.toFrame (Pullback.lift f p) :=
  s.pullbackLift_pullbackToFrame f p

/-- If `s.toFrame ⟨f y, p⟩` is the frame `φ` at `f y`, then `(s.pullback f).toFrame ⟨y, p⟩` is the
same frame viewed in the pullback fibre at `y`. -/
theorem toFrame_pullback_mk (s : OrthonormalFrameLift F E n G ρ) (f : K) (y : Y) (p : s.P (f y))
    {φ : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] E (f y)} (h : s.toFrame ⟨f y, p⟩ = ⟨f y, φ⟩) :
    (s.pullback f).toFrame (⟨y, p⟩ : TotalSpace G (s.pullback f).P) =
      (⟨y, φ⟩ : OrthonormalFrameBundle ℝ F ((f : Y → X) *ᵖ E) (EuclideanSpace ℝ (Fin n))) := by
  apply (OrthonormalFrameBundle.pullbackHomeomorph (f : Y → X)).injective
  apply Subtype.ext
  simp only [OrthonormalFrameBundle.pullbackHomeomorph_apply,
    OrthonormalFrameBundle.pullbackLift_mk]
  exact Prod.ext ((s.pullback f).proj_toFrame ⟨y, p⟩)
    ((s.pullbackLift_toFrame_pullback f ⟨y, p⟩).trans h)

/-- The **pullback of an equivalence** of lifts along a continuous map: equivalences
commute with pullback. -/
noncomputable def Equiv.pullback {s t : OrthonormalFrameLift F E n G ρ} (φ : s.Equiv t) (f : K) :
    (s.pullback f).Equiv (t.pullback f) where
  toEquiv y := φ.toEquiv (f y)
  continuous_toFun := (Pullback.continuous_iff (f := (f : Y → X))
    (g := fun p : TotalSpace _ ((f : Y → X) *ᵖ s.P) ↦
      (⟨p.proj, φ.toEquiv (f p.proj) p.snd⟩ : TotalSpace _ ((f : Y → X) *ᵖ t.P)))).2
    ⟨Pullback.continuous_proj _ _ _, φ.continuous_toFun.comp (Pullback.continuous_lift _ _ _)⟩
  continuous_invFun := (Pullback.continuous_iff (f := (f : Y → X))
    (g := fun p : TotalSpace _ ((f : Y → X) *ᵖ t.P) ↦
      (⟨p.proj, (φ.toEquiv (f p.proj)).symm p.snd⟩ : TotalSpace _ ((f : Y → X) *ᵖ s.P)))).2
    ⟨Pullback.continuous_proj _ _ _, φ.continuous_invFun.comp (Pullback.continuous_lift _ _ _)⟩
  map_smul y p g := φ.map_smul (f y) p g
  toFrame_map y p := by
    simp only [pullback_toFrame, pullbackToFrame]
    congr 2
    exact Prod.ext rfl (φ.toFrame_map (f y) p)

@[simp]
theorem Equiv.pullback_toEquiv {s t : OrthonormalFrameLift F E n G ρ} (φ : s.Equiv t) (f : K)
    (y : Y) :
    (φ.pullback f).toEquiv y = φ.toEquiv (f y) :=
  (rfl)

@[simp]
theorem Equiv.toFrame_pullback_toEquiv {s t : OrthonormalFrameLift F E n G ρ} (φ : s.Equiv t)
    (f : K) (y : Y) (p : s.P (f y)) :
    (t.pullback f).toFrame ⟨y, φ.toEquiv (f y) p⟩ = (s.pullback f).toFrame ⟨y, p⟩ :=
  (φ.pullback f).toFrame_map y p

@[simp]
theorem Equiv.toFrame_pullback_toEquiv_symm {s t : OrthonormalFrameLift F E n G ρ}
    (φ : s.Equiv t) (f : K) (y : Y) (p : t.P (f y)) :
    (s.pullback f).toFrame ⟨y, (φ.toEquiv (f y)).symm p⟩ = (t.pullback f).toFrame ⟨y, p⟩ :=
  (φ.pullback f).toFrame_map_symm y p

@[simp]
theorem Equiv.pullback_refl (s : OrthonormalFrameLift F E n G ρ) (f : K) :
    (refl s).pullback f = refl (s.pullback f) :=
  (rfl)

@[simp]
theorem Equiv.pullback_symm {s t : OrthonormalFrameLift F E n G ρ} (φ : s.Equiv t) (f : K) :
    φ.symm.pullback f = (φ.pullback f).symm :=
  (rfl)

@[simp]
theorem Equiv.pullback_trans {s t u : OrthonormalFrameLift F E n G ρ} (φ : s.Equiv t)
    (ψ : t.Equiv u) (f : K) : (φ.trans ψ).pullback f = (φ.pullback f).trans (ψ.pullback f) :=
  (rfl)

/-- The homeomorphism of total spaces induced by the pullback of an equivalence lifts to the one
induced by the equivalence. -/
theorem Equiv.lift_pullback_toHomeomorph {s t : OrthonormalFrameLift F E n G ρ} (φ : s.Equiv t)
    (f : K) (p : TotalSpace G (s.pullback f).P) :
    Pullback.lift f ((φ.pullback f).toHomeomorph p) = φ.toHomeomorph (Pullback.lift f p) :=
  (rfl)

end Pullback

/-! ### Transport along fibrewise isometries -/

section Map

variable {F' : Type*} {E' : X → Type w} [TopologicalSpace (TotalSpace F' E')]
  [∀ x, NormedAddCommGroup (E' x)] [∀ x, InnerProductSpace ℝ (E' x)]
  {F'' : Type*} {E'' : X → Type w} [TopologicalSpace (TotalSpace F'' E'')]
  [∀ x, NormedAddCommGroup (E'' x)] [∀ x, InnerProductSpace ℝ (E'' x)]

/-- The **transport of a lift along fibrewise isometries** `Φ x : E x ≃ₗᵢ[ℝ] E' x` forming a
continuous map of total spaces: the same principal bundle `P`, with the frame of a point composed
with `Φ` (`TauCeti.OrthonormalFrameBundle.map`). Its body is exposed so that the fibre
`(s.map Φ hΦ).P x` unfolds to `s.P x` downstream. -/
@[expose]
noncomputable def map (s : OrthonormalFrameLift F E n G ρ) (Φ : ∀ x, E x ≃ₗᵢ[ℝ] E' x)
    (hΦ : Continuous fun v : TotalSpace F E ↦ (⟨v.proj, Φ v.proj v.snd⟩ : TotalSpace F' E')) :
    OrthonormalFrameLift F' E' n G ρ where
  P := s.P
  toFrame p := OrthonormalFrameBundle.map Φ (s.toFrame p)
  continuous_toFrame := (OrthonormalFrameBundle.continuous_map hΦ).comp s.continuous_toFrame
  proj_toFrame p := (OrthonormalFrameBundle.proj_map Φ _).trans (s.proj_toFrame p)
  toFrame_smul x p g v := by
    have h := congrArg (fun q : TotalSpace F E ↦ (⟨q.proj, Φ q.proj q.snd⟩ : TotalSpace F' E'))
      (s.toFrame_smul x p g v)
    simpa only [TotalSpace.mk', OrthonormalFrameBundle.totalSpaceMk_map_frame] using h

variable {Φ : ∀ x, E x ≃ₗᵢ[ℝ] E' x}
  {hΦ : Continuous fun v : TotalSpace F E ↦ (⟨v.proj, Φ v.proj v.snd⟩ : TotalSpace F' E')}

@[simp]
theorem map_P (s : OrthonormalFrameLift F E n G ρ) : (s.map Φ hΦ).P = s.P :=
  rfl

/-- The frame of a point of the transported lift is its frame in `s`, composed with `Φ`. -/
@[simp]
theorem toFrame_map (s : OrthonormalFrameLift F E n G ρ) (p : TotalSpace G s.P) :
    (s.map Φ hΦ).toFrame p = OrthonormalFrameBundle.map Φ (s.toFrame p) :=
  rfl

/-- Transport along the identity isometries is the identity. -/
@[simp]
theorem map_refl (s : OrthonormalFrameLift F E n G ρ) :
    s.map (fun x ↦ LinearIsometryEquiv.refl ℝ (E x)) continuous_id = s := by
  cases s
  simp only [map, OrthonormalFrameBundle.map_refl]

/-- Successive transports compose as the families of isometries do. -/
@[simp]
theorem map_map (s : OrthonormalFrameLift F E n G ρ) {Ψ : ∀ x, E' x ≃ₗᵢ[ℝ] E'' x}
    (hΨ : Continuous fun v : TotalSpace F' E' ↦ (⟨v.proj, Ψ v.proj v.snd⟩ : TotalSpace F'' E'')) :
    (s.map Φ hΦ).map Ψ hΨ = s.map (fun x ↦ (Φ x).trans (Ψ x)) (hΨ.comp hΦ) := by
  cases s
  simp only [map, OrthonormalFrameBundle.map_map]

/-- Transport along `Φ` followed by transport along the inverse isometries is the identity. -/
theorem map_symm_map (s : OrthonormalFrameLift F E n G ρ)
    (h : Continuous fun v : TotalSpace F' E' ↦
      (⟨v.proj, (Φ v.proj).symm v.snd⟩ : TotalSpace F E)) :
    (s.map Φ hΦ).map (fun x ↦ (Φ x).symm) h = s := by
  rw [map_map]
  simp only [LinearIsometryEquiv.self_trans_symm]
  exact map_refl s

/-- Transport along the inverse isometries followed by transport along `Φ` is the identity. -/
theorem map_map_symm (s : OrthonormalFrameLift F' E' n G ρ)
    (h : Continuous fun v : TotalSpace F' E' ↦
      (⟨v.proj, (Φ v.proj).symm v.snd⟩ : TotalSpace F E)) :
    (s.map (fun x ↦ (Φ x).symm) h).map Φ hΦ = s := by
  rw [map_map]
  simp only [LinearIsometryEquiv.symm_trans_self]
  exact map_refl s

/-- Transport along fibrewise isometries is injective on lifts. -/
theorem map_injective :
    Function.Injective fun s : OrthonormalFrameLift F E n G ρ ↦ s.map Φ hΦ := by
  rintro ⟨P, toFrame, _, _, _⟩ ⟨P', toFrame', _, _, _⟩ hst
  simp only [map, mk.injEq] at hst
  obtain ⟨rfl, h₁, h₂, h₃, h₄, h₅⟩ := hst
  cases h₁; cases h₂; cases h₃; cases h₄
  have : toFrame = toFrame' := funext fun p ↦
    OrthonormalFrameBundle.map_right_injective Φ (congrFun (eq_of_heq h₅) p)
  subst this
  rfl

/-- Every lift for `E'` is the transport of a lift for `E` along fibrewise isometries. -/
theorem map_surjective
    (h : Continuous fun v : TotalSpace F' E' ↦
      (⟨v.proj, (Φ v.proj).symm v.snd⟩ : TotalSpace F E)) :
    Function.Surjective fun s : OrthonormalFrameLift F E n G ρ ↦ s.map Φ hΦ := fun s ↦
  ⟨s.map (fun x ↦ (Φ x).symm) h, s.map_map_symm h⟩

/-- The **transport of an equivalence of lifts** along fibrewise isometries: the same bijections
between fibres. -/
def Equiv.map {s t : OrthonormalFrameLift F E n G ρ} (φ : s.Equiv t) (Φ : ∀ x, E x ≃ₗᵢ[ℝ] E' x)
    (hΦ : Continuous fun v : TotalSpace F E ↦ (⟨v.proj, Φ v.proj v.snd⟩ : TotalSpace F' E')) :
    (s.map Φ hΦ).Equiv (t.map Φ hΦ) where
  toEquiv := φ.toEquiv
  continuous_toFun := φ.continuous_toFun
  continuous_invFun := φ.continuous_invFun
  map_smul := φ.map_smul
  toFrame_map x p := congrArg (OrthonormalFrameBundle.map Φ) (φ.toFrame_map x p)

@[simp]
theorem Equiv.map_toEquiv {s t : OrthonormalFrameLift F E n G ρ} (φ : s.Equiv t) (x : X) :
    (φ.map Φ hΦ).toEquiv x = φ.toEquiv x :=
  (rfl)

@[simp]
theorem Equiv.map_refl (s : OrthonormalFrameLift F E n G ρ) :
    (refl s).map Φ hΦ = refl (s.map Φ hΦ) :=
  (rfl)

@[simp]
theorem Equiv.map_symm {s t : OrthonormalFrameLift F E n G ρ} (φ : s.Equiv t) :
    φ.symm.map Φ hΦ = (φ.map Φ hΦ).symm :=
  (rfl)

@[simp]
theorem Equiv.map_trans {s t u : OrthonormalFrameLift F E n G ρ} (φ : s.Equiv t)
    (ψ : t.Equiv u) : (φ.trans ψ).map Φ hΦ = (φ.map Φ hΦ).trans (ψ.map Φ hΦ) :=
  (rfl)

/-- **Successive transports of an equivalence compose**: once the source and target lifts are
identified by `TauCeti.OrthonormalFrameLift.map_map`, transporting `φ` along `Φ` and then along `Ψ`
is transporting it along the composite isometries. All act on the fibre over `x` by
`φ.toEquiv x`. -/
theorem Equiv.map_map_heq {s t : OrthonormalFrameLift F E n G ρ} (φ : s.Equiv t)
    {Ψ : ∀ x, E' x ≃ₗᵢ[ℝ] E'' x}
    (hΨ : Continuous fun v : TotalSpace F' E' ↦ (⟨v.proj, Ψ v.proj v.snd⟩ : TotalSpace F'' E'')) :
    HEq ((φ.map Φ hΦ).map Ψ hΨ) (φ.map (fun x ↦ (Φ x).trans (Ψ x)) (hΨ.comp hΦ)) :=
  heq_of_toEquiv_heq (s.map_map hΨ) (t.map_map hΨ) fun _ ↦ HEq.rfl

/-- **Transport of an equivalence along the identity isometries** is the equivalence itself, once
the source and target lifts are identified by `TauCeti.OrthonormalFrameLift.map_refl`. -/
theorem Equiv.map_refl_heq {s t : OrthonormalFrameLift F E n G ρ} (φ : s.Equiv t) :
    HEq (φ.map (fun x ↦ LinearIsometryEquiv.refl ℝ (E x)) continuous_id) φ :=
  heq_of_toEquiv_heq (s.map_refl) (t.map_refl) fun _ ↦ HEq.rfl

/-- An equivalence between transported lifts is an equivalence between the original lifts: the
frame maps of `s` and `t` agree once composed with the injective map of frame bundles induced by
`Φ`. -/
def Equiv.ofMap {s t : OrthonormalFrameLift F E n G ρ} (φ : (s.map Φ hΦ).Equiv (t.map Φ hΦ)) :
    s.Equiv t where
  toEquiv := φ.toEquiv
  continuous_toFun := φ.continuous_toFun
  continuous_invFun := φ.continuous_invFun
  map_smul := φ.map_smul
  toFrame_map x p := OrthonormalFrameBundle.map_right_injective Φ (φ.toFrame_map x p)

@[simp]
theorem Equiv.ofMap_toEquiv {s t : OrthonormalFrameLift F E n G ρ}
    (φ : (s.map Φ hΦ).Equiv (t.map Φ hΦ)) (x : X) : φ.ofMap.toEquiv x = φ.toEquiv x :=
  (rfl)

@[simp]
theorem Equiv.ofMap_map {s t : OrthonormalFrameLift F E n G ρ} (φ : s.Equiv t) :
    (φ.map Φ hΦ).ofMap = φ :=
  (rfl)

@[simp]
theorem Equiv.map_ofMap {s t : OrthonormalFrameLift F E n G ρ}
    (φ : (s.map Φ hΦ).Equiv (t.map Φ hΦ)) : φ.ofMap.map Φ hΦ = φ :=
  (rfl)

@[simp]
theorem Equiv.ofMap_refl (s : OrthonormalFrameLift F E n G ρ) :
    (refl (s.map Φ hΦ)).ofMap = refl s :=
  (rfl)

@[simp]
theorem Equiv.ofMap_symm {s t : OrthonormalFrameLift F E n G ρ}
    (φ : (s.map Φ hΦ).Equiv (t.map Φ hΦ)) : φ.symm.ofMap = φ.ofMap.symm :=
  (rfl)

@[simp]
theorem Equiv.ofMap_trans {s t u : OrthonormalFrameLift F E n G ρ}
    (φ : (s.map Φ hΦ).Equiv (t.map Φ hΦ)) (ψ : (t.map Φ hΦ).Equiv (u.map Φ hΦ)) :
    (φ.trans ψ).ofMap = φ.ofMap.trans ψ.ofMap :=
  (rfl)

/-- Transport does not change the homeomorphism of total spaces induced by an equivalence. -/
@[simp]
theorem Equiv.map_toHomeomorph {s t : OrthonormalFrameLift F E n G ρ} (φ : s.Equiv t) :
    (φ.map Φ hΦ).toHomeomorph = φ.toHomeomorph :=
  (rfl)

@[simp]
theorem Equiv.ofMap_toHomeomorph {s t : OrthonormalFrameLift F E n G ρ}
    (φ : (s.map Φ hΦ).Equiv (t.map Φ hΦ)) : φ.ofMap.toHomeomorph = φ.toHomeomorph :=
  (rfl)

/-- Transport along fibrewise isometries identifies the equivalences of two lifts with the
equivalences of their transports. -/
def equivMapEquiv (Φ : ∀ x, E x ≃ₗᵢ[ℝ] E' x)
    (hΦ : Continuous fun v : TotalSpace F E ↦ (⟨v.proj, Φ v.proj v.snd⟩ : TotalSpace F' E'))
    (s t : OrthonormalFrameLift F E n G ρ) :
    s.Equiv t ≃ (s.map Φ hΦ).Equiv (t.map Φ hΦ) where
  toFun φ := φ.map Φ hΦ
  invFun φ := φ.ofMap
  left_inv := Equiv.ofMap_map
  right_inv := Equiv.map_ofMap

@[simp]
theorem equivMapEquiv_apply (s t : OrthonormalFrameLift F E n G ρ) (φ : s.Equiv t) :
    equivMapEquiv Φ hΦ s t φ = φ.map Φ hΦ :=
  (rfl)

@[simp]
theorem equivMapEquiv_symm_apply (s t : OrthonormalFrameLift F E n G ρ)
    (φ : (s.map Φ hΦ).Equiv (t.map Φ hΦ)) : (equivMapEquiv Φ hΦ s t).symm φ = φ.ofMap :=
  (rfl)

/-- Two lifts are equivalent exactly when their transports along fibrewise isometries are:
transport is injective on equivalence classes of lifts. When the inverse isometries are continuous
too, transport is surjective on lifts (`TauCeti.OrthonormalFrameLift.map_surjective`), hence a
bijection on equivalence classes. -/
theorem nonempty_equiv_map_iff (s t : OrthonormalFrameLift F E n G ρ) :
    Nonempty ((s.map Φ hΦ).Equiv (t.map Φ hΦ)) ↔ Nonempty (s.Equiv t) :=
  (equivMapEquiv Φ hΦ s t).nonempty_congr.symm

variable {Y : Type*} [TopologicalSpace Y] {K : Type*} [FunLike K Y X] [ContinuousMapClass K Y X]

/-- **Transport commutes with pullback**: pulling back the transport of `s` along `Φ` is
transporting the pullback of `s` along the pulled-back isometries `Φ (f y)`. -/
theorem pullback_map (s : OrthonormalFrameLift F E n G ρ) (f : K) :
    (s.map Φ hΦ).pullback f =
      (s.pullback f).map (E' := (f : Y → X) *ᵖ E') (fun y ↦ Φ (f y))
        (Pullback.continuous_fiberwise (Φ := fun x ↦ Φ x) hΦ f) := by
  have h (p : TotalSpace G ((f : Y → X) *ᵖ s.P)) :
      (s.map Φ hΦ).pullbackToFrame f p =
        OrthonormalFrameBundle.map (E' := (f : Y → X) *ᵖ E') (fun y ↦ Φ (f y))
          (s.pullbackToFrame f p) := by
    apply (OrthonormalFrameBundle.pullbackHomeomorph (f : Y → X)).injective
    apply Subtype.ext
    simp only [OrthonormalFrameBundle.pullbackHomeomorph_apply,
      OrthonormalFrameBundle.pullbackLift_map, pullbackLift_pullbackToFrame]
    exact Prod.ext (((s.map Φ hΦ).proj_pullbackToFrame f p).trans
        ((OrthonormalFrameBundle.proj_map _ _).trans (s.proj_pullbackToFrame f p)).symm)
      ((s.map Φ hΦ).pullbackLift_pullbackToFrame f p)
  simp only [pullback, map]
  congr 1
  exact funext h

/-- **Transport of equivalences commutes with pullback**: once the source and target lifts are
identified by `TauCeti.OrthonormalFrameLift.pullback_map`, pulling back the transport of `φ` along
`Φ` is transporting the pullback of `φ` along the pulled-back isometries `Φ (f y)`. Both act on the
fibre over `y` by `φ.toEquiv (f y)`. -/
theorem Equiv.pullback_map_heq {s t : OrthonormalFrameLift F E n G ρ} (φ : s.Equiv t) (f : K) :
    HEq ((φ.map Φ hΦ).pullback f)
      ((φ.pullback f).map (E' := (f : Y → X) *ᵖ E') (fun y ↦ Φ (f y))
        (Pullback.continuous_fiberwise (Φ := fun x ↦ Φ x) hΦ f)) :=
  -- Both equivalences have the same bijections, between fibres identified by `pullback_map`.
  Equiv.heq_of_toEquiv_heq (s.pullback_map f) (t.pullback_map f) fun _ ↦ HEq.rfl

end Map

/-! ### Changing the model frame -/

/-- The **lift with precomposed frames**: for a lift `s` along `ρ`, a linear isometry `r` of the
model `ℝⁿ` and a homomorphism `ρ'` with `ρ g ∘ r = r ∘ ρ' g`, the lift along `ρ'` with the same
principal bundle, whose frame at `p` is the frame of `p` in `s` precomposed with `r`. Its body is
exposed so that the fibre `(s.precomp r ρ' hr).P x` unfolds to `s.P x` downstream. -/
@[expose]
noncomputable def precomp (s : OrthonormalFrameLift F E n G ρ)
    (r : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n))
    (ρ' : G →* (Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ))
    (hr : ∀ g v, ρ g (r (WithLp.toLp 2 v)).ofLp = (r (WithLp.toLp 2 (ρ' g v))).ofLp) :
    OrthonormalFrameLift F E n G ρ' where
  P := s.P
  toFrame p := ⟨(s.toFrame p).proj, r.trans (s.toFrame p).frame⟩
  continuous_toFrame := OrthonormalFrameBundle.continuous_iff.2 fun v ↦
    (OrthonormalFrameBundle.continuous_totalSpaceMk_frame (r v)).comp s.continuous_toFrame
  proj_toFrame p := s.proj_toFrame p
  toFrame_smul x p g v := by
    have h := s.toFrame_smul x p g (r (WithLp.toLp 2 v)).ofLp
    simp only [WithLp.toLp_ofLp, hr] at h
    simpa only [LinearIsometryEquiv.trans_apply] using h

/-- The frame of a point in the lift with precomposed frames is its frame in the original lift
precomposed with `r`. -/
@[simp]
theorem toFrame_precomp (s : OrthonormalFrameLift F E n G ρ)
    (r : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n))
    (ρ' : G →* (Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ))
    (hr : ∀ g v, ρ g (r (WithLp.toLp 2 v)).ofLp = (r (WithLp.toLp 2 (ρ' g v))).ofLp)
    (p : TotalSpace G s.P) :
    (s.precomp r ρ' hr).toFrame p = ⟨(s.toFrame p).proj, r.trans (s.toFrame p).frame⟩ :=
  (rfl)

/-- **Precomposing frames is functorial**: an equivalence `s ≃ t` of lifts is an equivalence of
the lifts with frames precomposed with `r`. -/
noncomputable def Equiv.precomp {s t : OrthonormalFrameLift F E n G ρ} (φ : s.Equiv t)
    (r : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n))
    (ρ' : G →* (Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ))
    (hr : ∀ g v, ρ g (r (WithLp.toLp 2 v)).ofLp = (r (WithLp.toLp 2 (ρ' g v))).ofLp) :
    (s.precomp r ρ' hr).Equiv (t.precomp r ρ' hr) where
  toEquiv := φ.toEquiv
  continuous_toFun := φ.continuous_toFun
  continuous_invFun := φ.continuous_invFun
  map_smul := φ.map_smul
  -- `rw` and `simp` cannot see through the fibre `(s.precomp …).P x = s.P x`, so the frame
  -- equation of `φ` is pushed through the precomposition `q ↦ ⟨q.proj, r.trans q.frame⟩` of the
  -- frame map (`toFrame_precomp`) by `congrArg`.
  toFrame_map x p := congrArg (fun q ↦ (⟨q.proj, r.trans q.frame⟩ :
    OrthonormalFrameBundle ℝ F E (EuclideanSpace ℝ (Fin n)))) (φ.toFrame_map x p)

@[simp]
theorem Equiv.precomp_toEquiv {s t : OrthonormalFrameLift F E n G ρ} (φ : s.Equiv t)
    (r : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n))
    (ρ' : G →* (Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ))
    (hr : ∀ g v, ρ g (r (WithLp.toLp 2 v)).ofLp = (r (WithLp.toLp 2 (ρ' g v))).ofLp) (x : X) :
    (φ.precomp r ρ' hr).toEquiv x = φ.toEquiv x :=
  (rfl)

end OrthonormalFrameLift

end TauCeti
