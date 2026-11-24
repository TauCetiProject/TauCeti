/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SemilocallySimplyConnected.On
public import TauCeti.Topology.PathSpace.Seamed.Basic
import TauCeti.Topology.Homotopy.Homotopic.With

/-!
# Path components of seamed path spaces

For a continuous self-map `φ` of a space `X`, the `φ`-seamed paths `γ : [0, 1] → X`, with
`γ 1 = φ (γ 0)`, form the space `TauCeti.SeamedPath φ`. A path in this space is a homotopy of
paths whose end is kept equal to the image of its start under `φ`. This file shows that, when `X`
is semilocally simply connected and locally path-connected, as every manifold is, the path
components of `SeamedPath φ` are open, hence clopen
(`TauCeti.SeamedPath.isClopen_pathComponent`). So the set of seamed paths in a given component is
locally constant along any continuous family of seamed paths. For `φ = id` these components are
the free homotopy classes of loops, and the statement is the seamed analogue of
`TauCeti.isClopen_setOf_homotopic_refl`.

Two moves join seamed paths.

* A homotopy of paths from `x` to `φ x` relative to the endpoints keeps the seam
  (`TauCeti.SeamedPath.joined_ofPath_of_homotopic`).
* The start point can slide along a path `c` from `x` to `x'`, the end sliding along its image
  `φ ∘ c`: the seamed path `p` is joined to `c⁻¹ · p · (φ ∘ c)`
  (`TauCeti.SeamedPath.joined_ofPath_trans_trans`), through the seamed paths that first run back
  along `c` from `c s` to `x`, then along `p`, and then along `φ ∘ c` from `φ x` to `φ (c s)`.

A seamed path `γ` close to `γ₀` lies in a tube around `γ₀` and starts close to the start `a` of
`γ₀`. Slide the start of `γ₀` along a short path `c` from `a` to the start of `γ`, inside the first
vertex set of the tube and inside the preimage under `φ` of its last vertex set. Then
`c⁻¹ · γ₀ · (φ ∘ c)` and `γ` have the same endpoints, and they are homotopic by the conjugation of
paths in a common tube (`Path.IsInTube.trans_homotopic_trans`). So every seamed path close to `γ₀`
is joined to it (`TauCeti.SeamedPath.eventually_joined`).

## Main results

* `TauCeti.SeamedPath.joined_ofPath_of_homotopic`: homotopic paths from `x` to `φ x` are joined
  as seamed paths.
* `TauCeti.SeamedPath.joined_ofPath_trans_trans`: sliding the start point of a seamed path along a
  path stays in its path component.
* `TauCeti.SeamedPath.eventually_joined`: seamed paths close to a given one are joined to it.
* `TauCeti.SeamedPath.isClopen_pathComponent`: the path components of `SeamedPath φ` are clopen.

## References

* A. Floer, *Symplectic fixed points and holomorphic spheres*, Comm. Math. Phys. 120 (1989),
  575–611.
-/

public section

open Filter Set Topology unitInterval

namespace TauCeti

namespace SeamedPath

variable {X : Type*} [TopologicalSpace X] {φ : X → X}

/-- **Homotopic paths are joined seamed paths.** A homotopy relative to the endpoints between two
paths from `x` to `φ x` is a path of `φ`-seamed paths. -/
theorem joined_ofPath_of_homotopic {x : X} {p q : Path x (φ x)} (h : p.Homotopic q) :
    Joined (ofPath p) (ofPath q) := by
  obtain ⟨F⟩ := h
  refine (ContinuousMap.homotopicWith_iff_joined (ofPath p).property (ofPath q).property).1 ?_
  rw [val_ofPath, val_ofPath]
  exact ⟨⟨F.toHomotopy, fun t ↦ by simp⟩⟩

/-- **Sliding the start point of a seamed path.** For continuous `φ`, a path `p` from `x` to `φ x`
and a path `c` from `x` to `x'`, the `φ`-seamed paths `p` and `c⁻¹ · p · (φ ∘ c)` are joined. The
path between them runs through the seamed paths `(c|[0, s])⁻¹ · p · (φ ∘ c|[0, s])`. -/
theorem joined_ofPath_trans_trans (hφ : Continuous φ) {x x' : X} (c : Path x x')
    (p : Path x (φ x)) : Joined (ofPath p) (ofPath ((c.symm.trans p).trans (c.map hφ))) := by
  -- The seamed paths that run back along `c` from `c s` to `x`, along `p`, and along `φ ∘ c`.
  let p' : Path (c 0) (φ (c 0)) := p.cast c.source (by rw [c.source])
  let slide : ∀ s : I, Path (c s) (φ (c s)) := fun s ↦
    ((c.subpath 0 s).symm.trans p').trans ((c.subpath 0 s).map hφ)
  have hsub : Continuous ↿fun s : I ↦ c.subpath 0 s :=
    c.subpath_continuous_family.comp (continuous_const.prodMk continuous_id :
      Continuous fun q : I × I ↦ ((0 : I), q))
  have hslide : Continuous ↿slide :=
    Path.trans_continuous_family _ (Path.trans_continuous_family _
      (Path.symm_continuous_family _ hsub) _ (p.continuous.comp continuous_snd)) _
      (hφ.comp hsub)
  -- At `s = 0` the slide is `p` with constant paths attached at both ends.
  have h₀ : (slide 0).Homotopic p' := by
    simp only [slide, Path.subpath_self, Path.refl_symm, Path.map_refl]
    exact (Path.Homotopic.trans_refl _).trans (Path.Homotopic.refl_trans _)
  -- At `s = 1` it is `c⁻¹ · p · (φ ∘ c)`.
  have h₁ : ofPath (slide 1) = ofPath ((c.symm.trans p).trans (c.map hφ)) :=
    ext fun t ↦ by
      simp only [slide, p', Path.subpath_zero_one]
      simp [Path.trans_apply]
  have hp : ofPath p = ofPath p' := ext fun _ ↦ by simp [p']
  rw [← h₁, hp]
  exact (joined_ofPath_of_homotopic h₀).symm.trans
    ⟨{ toFun := fun s ↦ ofPath (slide s)
       continuous_toFun := continuous_induced_rng.2 <|
         ContinuousMap.continuous_of_continuous_uncurry _ <| by
           simp only [Function.comp_def, val_ofPath, Function.uncurry_def]
           exact hslide
       source' := rfl
       target' := rfl }⟩

variable [LocallyPathConnectedSpace X] [SemilocallySimplyConnectedSpace X]

/-- **Nearby seamed paths are joined.** In a semilocally simply connected, locally path-connected
space, every `φ`-seamed path close enough to `γ₀` in the compact-open topology is joined to `γ₀`
in `SeamedPath φ`. -/
theorem eventually_joined (hφ : Continuous φ) (γ₀ : SeamedPath φ) :
    ∀ᶠ γ in 𝓝 γ₀, Joined γ γ₀ := by
  obtain ⟨n, part, T, hT⟩ := γ₀.toPath.exists_isInTube_of_semilocallySimplyConnectedOn
    (.of_semilocallySimplyConnectedSpace _)
  -- Start points are slid inside `W`: the first vertex set of the tube, intersected with the
  -- preimage under `φ` of its last vertex set.
  set W := T.V 0 ∩ φ ⁻¹' T.V (Fin.last n)
  have ha : γ₀.val 0 ∈ W := by
    have h₀ := hT.mem_V 0
    have h₁ := hT.mem_V (Fin.last n)
    rw [part.t_zero, Path.source] at h₀
    rw [part.t_last, Path.target] at h₁
    exact ⟨h₀, h₁⟩
  have hW : IsOpen W := (T.isOpen_V 0).inter ((T.isOpen_V _).preimage hφ)
  have htube : ∀ᶠ γ in 𝓝 γ₀, Path.IsInTube (toPath γ) part T := by
    filter_upwards [((T.isOpen_setOf_isInTube part).preimage continuous_subtypeVal).mem_nhds
      (show γ₀.val ∈ {f : C(I, X) | Path.IsInTube f part T} by simpa using hT)] with γ hγ
    simpa using hγ
  have hstart : ∀ᶠ γ in 𝓝 γ₀, (γ : SeamedPath φ).val 0 ∈ pathComponentIn W (γ₀.val 0) :=
    ((hW.pathComponentIn _).preimage ((continuous_eval_const 0).comp
      continuous_subtypeVal)).mem_nhds (mem_pathComponentIn_self ha)
  filter_upwards [htube, hstart] with γ hγ hγW
  set c := hγW.somePath
  have hc : range c ⊆ W := range_subset_iff.mpr hγW.somePath_mem
  have hcφ : range (c.map hφ) ⊆ T.V (Fin.last n) := by
    rintro _ ⟨t, rfl⟩
    exact (hc ⟨t, rfl⟩).2
  -- In the tube, `γ₀ · (φ ∘ c) ≃ c · γ`, so `c⁻¹ · γ₀ · (φ ∘ c) ≃ γ`.
  have key := hT.trans_homotopic_trans hγ (hc.trans inter_subset_left) hcφ
  have hhom : ((c.symm.trans γ₀.toPath).trans (c.map hφ)).Homotopic γ.toPath :=
    (Path.Homotopic.trans_assoc _ _ _).trans <| ((Path.Homotopic.refl c.symm).hcomp key).trans <|
      (Path.Homotopic.trans_assoc _ _ _).symm.trans <|
        Path.Homotopic.trans_left_of_nullhomotopic (Path.Homotopic.symm_trans c)
  have h := (joined_ofPath_trans_trans hφ c γ₀.toPath).trans (joined_ofPath_of_homotopic hhom)
  rw [ofPath_toPath, ofPath_toPath] at h
  exact h.symm

/-- **The path components of a seamed path space are open.** -/
theorem isOpen_pathComponent (hφ : Continuous φ) (γ : SeamedPath φ) :
    IsOpen (pathComponent γ) :=
  isOpen_iff_mem_nhds.mpr fun _ hγ' ↦
    (eventually_joined hφ _).mono fun _ h ↦ (mem_pathComponent_iff.mp hγ').trans h.symm

/-- **The path components of a seamed path space are clopen.** In a semilocally simply connected,
locally path-connected space, for instance a manifold, the path components of the space of
`φ`-seamed paths of a continuous map `φ` are open and closed. -/
theorem isClopen_pathComponent (hφ : Continuous φ) (γ : SeamedPath φ) :
    IsClopen (pathComponent γ) := by
  refine ⟨isOpen_compl_iff.mp <| isOpen_iff_mem_nhds.mpr fun γ' hγ' ↦ ?_,
    isOpen_pathComponent hφ γ⟩
  exact (eventually_joined hφ γ').mono fun _ h h' ↦ hγ' ((mem_pathComponent_iff.mp h').trans h)

end SeamedPath

end TauCeti
