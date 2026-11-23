/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.FiberBundle.Principal.Basic
public import TauCeti.Topology.VectorBundle.OrthonormalFrame.Pullback

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

An *equivalence* of lifts (`TauCeti.OrthonormalFrameLift.Equiv`) is a family of equivariant
bijections between the fibres of the two principal bundles, inducing a homeomorphism of total
spaces (`TauCeti.OrthonormalFrameLift.Equiv.toHomeomorph`) and commuting with the frame maps.
Equivalences have identities, inverses and composites.

The *pullback* of a lift along a continuous map `f : Y → X`
(`TauCeti.OrthonormalFrameLift.pullback`) is the pulled-back principal bundle `f *ᵖ P` with the
frame map read through the identification of the frames of `f *ᵖ E` at `y` with the frames of `E`
at `f y` (`TauCeti.OrthonormalFrameBundle.pullbackHomeomorph`). Equivalences pull back to
equivalences (`TauCeti.OrthonormalFrameLift.Equiv.pullback`).

## Main definitions

* `TauCeti.OrthonormalFrameLift`: a lift of the orthonormal frame bundle of a real vector bundle
  with fibre inner products along a homomorphism `ρ : G →* GL(ℝⁿ)`.
* `TauCeti.OrthonormalFrameLift.frameAt`: the orthonormal frame of `E x` at a point of `P`.
* `TauCeti.OrthonormalFrameLift.Equiv`: equivalences of lifts, with `refl`, `symm`, `trans`.
* `TauCeti.OrthonormalFrameLift.pullback`: the pullback of a lift along a continuous map.
* `TauCeti.OrthonormalFrameLift.Equiv.pullback`: the pullback of an equivalence.

## Main results

* `TauCeti.OrthonormalFrameLift.frameAt_smul`: the frame of `p • g` is the frame of `p`
  precomposed with `ρ g`.
* `TauCeti.OrthonormalFrameLift.finrank_fiber`, `TauCeti.OrthonormalFrameLift.finrank_model`:
  a bundle whose orthonormal frame bundle of rank `n` has a lift has fibres of dimension `n`.

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

/-- An **equivalence of lifts** `s ≃ t` on the same bundle: a family of bijections
between the fibres of their principal bundles, equivariant for the right action of `G`,
inducing continuous maps of total spaces in both directions, and commuting with the maps to the
orthonormal frame bundle. -/
structure Equiv (s t : OrthonormalFrameLift F E n G ρ) where
  /-- The bijection between fibres. -/
  toEquiv : ∀ x, s.P x ≃ t.P x
  /-- The induced map of total spaces is continuous. -/
  continuous_toFun : Continuous fun p : TotalSpace G s.P ↦
    (⟨p.proj, toEquiv p.proj p.snd⟩ : TotalSpace G t.P)
  /-- The inverse map of total spaces is continuous. -/
  continuous_invFun : Continuous fun p : TotalSpace G t.P ↦
    (⟨p.proj, (toEquiv p.proj).symm p.snd⟩ : TotalSpace G s.P)
  /-- The bijection is equivariant. -/
  map_smul : ∀ (x : X) (p : s.P x) (g : G),
    toEquiv x (op g • p) = op g • toEquiv x p
  /-- The bijection commutes with the maps to frames. -/
  toFrame_map : ∀ (x : X) (p : s.P x), t.toFrame ⟨x, toEquiv x p⟩ = s.toFrame ⟨x, p⟩

namespace Equiv

variable {s t u : OrthonormalFrameLift F E n G ρ}

attribute [simp] map_smul toFrame_map

/-- The inverse of the bijection of an equivalence is equivariant. -/
@[simp]
theorem map_smul_symm (φ : s.Equiv t) (x : X) (p : t.P x) (g : G) :
    (φ.toEquiv x).symm (op g • p) = op g • (φ.toEquiv x).symm p := by
  rw [_root_.Equiv.symm_apply_eq, φ.map_smul, _root_.Equiv.apply_symm_apply]

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
  funext x
  exact _root_.Equiv.ext (h x)

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
  toEquiv _ := _root_.Equiv.refl _
  continuous_toFun := continuous_id
  continuous_invFun := continuous_id
  map_smul _ _ _ := rfl
  toFrame_map _ _ := rfl

/-- The inverse of an equivalence of lifts. -/
@[symm]
def symm (φ : s.Equiv t) : t.Equiv s where
  toEquiv x := (φ.toEquiv x).symm
  continuous_toFun := φ.continuous_invFun
  continuous_invFun := φ.continuous_toFun
  map_smul := φ.map_smul_symm
  toFrame_map := φ.toFrame_map_symm

/-- The composite of two equivalences of lifts. -/
@[trans]
def trans (φ : s.Equiv t) (ψ : t.Equiv u) : s.Equiv u where
  toEquiv x := (φ.toEquiv x).trans (ψ.toEquiv x)
  continuous_toFun := ψ.continuous_toFun.comp φ.continuous_toFun
  continuous_invFun := φ.continuous_invFun.comp ψ.continuous_invFun
  map_smul x p g := by
    simp only [_root_.Equiv.trans_apply, φ.map_smul, ψ.map_smul]
  toFrame_map x p := by
    simp only [_root_.Equiv.trans_apply, ψ.toFrame_map, φ.toFrame_map]

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

end OrthonormalFrameLift

end TauCeti
