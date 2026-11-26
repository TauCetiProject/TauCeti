/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Distribution.Diffeomorph
public import TauCeti.Geometry.Manifold.Distribution.VectorBundle
public import TauCeti.Geometry.Manifold.VectorBundle.Quotient

/-!
# The quotient of the tangent bundle by a distribution

Let `D` be a `C^n` distribution of rank `k` on a manifold `M` of dimension `k + r`, modelled on a
finite-dimensional space over a complete field, and with `C^(n+1)` transition maps. The quotient
spaces `T_x M ⧸ D x`, each with its quotient topology, form a `C^n` vector bundle `TM ⧸ D` of rank
`r` (`TauCeti.IsContMDiffDistribution.contMDiffVectorBundle_quotientPrebundle`), whose local
trivializations are given by vector fields completing local frames of `D` to local frames of the
tangent bundle. The quotient map `TM → TM ⧸ D`, `(x, v) ↦ (x, [v])`, is `C^n`
(`TauCeti.IsContMDiffDistribution.contMDiff_totalSpace_mkQ`); on each fibre it is the quotient map
`Submodule.mkQ`, surjective with kernel `D x`. Every `C^n` section of `TM ⧸ D` is locally the
class of a `C^n` vector field (`TauCeti.IsContMDiffDistribution.exists_contMDiffOn_mk_eq`).

The construction is natural. A `C^(n+1)` map `f : M → M'` whose differential carries each `D x`
into `D' (f x)` induces the `C^n` map `TM ⧸ D → TM' ⧸ D'`, `(x, [v]) ↦ (f x, [df_x v])`
(`TauCeti.IsContMDiffDistribution.contMDiff_totalSpace_mapQ_mfderiv`). For a `C^(n+1)`
diffeomorphism `Φ` with `v ∈ D x ↔ dΦ_x v ∈ D' (Φ x)` this map is a `C^n` diffeomorphism of total
spaces covering `Φ` (`TauCeti.IsContMDiffDistribution.quotientDiffeomorph`), whose fibre maps are
the isomorphisms of normal spaces `IsLocalDiffeomorphAt.mfderivQuotientEquiv` and whose inverse is
induced by `Φ⁻¹`. It sends the identity to the identity and composites to composites.

For a hyperplane field `ξ`, of rank `dim M - 1`, this is the line bundle `TM ⧸ ξ`; when `ξ` is a
contact structure it is the contact line, in which the Levi form of `ξ`
(`TauCeti.distributionLeviForm`) takes its values. The construction is the specialization to the
tangent bundle of the quotient of a vector bundle by a subbundle with local frames,
`TauCeti.HasLocalContMDiffSubbundleFrames.quotientPrebundle`.

## Main definitions

* `TauCeti.IsContMDiffDistribution.quotientPrebundle`: the quotient bundle `TM ⧸ D`, as a vector
  prebundle with model fibre `Fin r → 𝕜`.
* `TauCeti.IsContMDiffDistribution.quotientDiffeomorph`: the isomorphism `TM ⧸ D ≃ TM' ⧸ D'`
  induced by a diffeomorphism carrying `D` onto `D'`.

## Main results

* `TauCeti.IsContMDiffDistribution.mem_pretrivializationAtlas_quotientPrebundle_iff`: the
  pretrivializations of `TM ⧸ D` are those of its `C^n` local frames.
* `TauCeti.IsContMDiffDistribution.contMDiffVectorBundle_quotientPrebundle`: `TM ⧸ D` is a `C^n`
  vector bundle.
* `trivializationOfMemPretrivializationAtlas_quotientPrebundle_apply`, in the namespace
  `TauCeti.IsContMDiffDistribution`: the trivializations of `TM ⧸ D` send a class to its
  coordinates in the corresponding frame.
* `TauCeti.IsContMDiffDistribution.contMDiff_totalSpace_mkQ`: the quotient map `TM → TM ⧸ D` is
  `C^n`.
* `TauCeti.IsContMDiffDistribution.exists_contMDiffOn_mk_eq`: `C^n` sections of `TM ⧸ D` lift
  locally to `C^n` vector fields.
* `TauCeti.IsContMDiffDistribution.contMDiff_totalSpace_mapQ_mfderiv`: the map of quotient bundles
  induced by the differential of a `C^(n+1)` map is `C^n`.
* `TauCeti.IsContMDiffDistribution.quotientDiffeomorph_mk`,
  `TauCeti.IsContMDiffDistribution.quotientDiffeomorph_symm_mk`: `[v] ↦ [dΦ v]` and
  `[w] ↦ [dΦ⁻¹ w]`.
* `TauCeti.IsContMDiffDistribution.quotientDiffeomorph_refl`,
  `TauCeti.IsContMDiffDistribution.quotientDiffeomorph_symm`,
  `TauCeti.IsContMDiffDistribution.quotientDiffeomorph_trans`: functoriality.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer GTM 218 (2013), Chapter 10
  (subbundles and local frames) and Chapter 19 (distributions).
-/

public section

noncomputable section

open Bundle Module
open scoped Manifold ContDiff

namespace TauCeti.IsContMDiffDistribution

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M] {n : ℕ∞ω}
  [IsManifold I (n + 1) M] {k r : ℕ} {D : Π x : M, Submodule 𝕜 (TangentSpace I x)}
  (hD : IsContMDiffDistribution I n k D) (hr : k + r = finrank 𝕜 E)

/-- **The quotient bundle `TM ⧸ D`** of a `C^n` distribution `D` of rank `k` on a manifold of
dimension `k + r`: the quotients `T_x M ⧸ D x`, with their quotient topologies, form a vector
prebundle with model fibre `Fin r → 𝕜`. Its pretrivializations are those of the `C^n` local
frames of `TM ⧸ D` (`TauCeti.IsQuotientFrameOn`). Install the total-space topology
`(hD.quotientPrebundle hr).totalSpaceTopology` and the fibre bundle structure
`(hD.quotientPrebundle hr).toFiberBundle` with `letI`. -/
def quotientPrebundle : VectorPrebundle 𝕜 (Fin r → 𝕜) fun x ↦ TangentSpace I x ⧸ D x :=
  have := TangentBundle.contMDiffVectorBundle (n := n) (I := I) (M := M)
  hD.hasLocalContMDiffSubbundleFrames.quotientPrebundle (by simpa using hr)

/-- The pretrivializations of the quotient bundle `TM ⧸ D` are those of the `C^n` local frames of
`TM ⧸ D` on open sets. -/
theorem mem_pretrivializationAtlas_quotientPrebundle_iff
    (e : Pretrivialization (Fin r → 𝕜) (π (Fin r → 𝕜) fun x ↦ TangentSpace I x ⧸ D x)) :
    e ∈ (hD.quotientPrebundle hr).pretrivializationAtlas ↔
      ∃ (U : Set M) (hU : IsOpen U) (Y : Fin r → Π x : M, TangentSpace I x)
        (hY : IsQuotientFrameOn D Y U), (∀ j, CMDiff[U] n (T% (Y j))) ∧
          hY.pretrivialization hU = e :=
  have := TangentBundle.contMDiffVectorBundle (n := n) (I := I) (M := M)
  hD.hasLocalContMDiffSubbundleFrames.mem_pretrivializationAtlas_quotientPrebundle_iff
    (by simpa using hr) e

/-- **The quotient of the tangent bundle by a `C^n` distribution is a `C^n` vector bundle.** -/
theorem contMDiffVectorBundle_quotientPrebundle :
    letI := (hD.quotientPrebundle hr).totalSpaceTopology
    letI := (hD.quotientPrebundle hr).toFiberBundle
    letI := (hD.quotientPrebundle hr).toVectorBundle
    ContMDiffVectorBundle n (Fin r → 𝕜) (fun x ↦ TangentSpace I x ⧸ D x) I :=
  have := TangentBundle.contMDiffVectorBundle (n := n) (I := I) (M := M)
  hD.hasLocalContMDiffSubbundleFrames.contMDiffVectorBundle_quotientPrebundle (by simpa using hr)

/-- In the quotient bundle `TM ⧸ D`, the trivialization given by a local frame `Y` of `TM ⧸ D` on
an open set `U` whose pretrivialization lies in the atlas sends a class over a point of `U` to its
coordinates in the frame. -/
theorem trivializationOfMemPretrivializationAtlas_quotientPrebundle_apply
    {Y : Fin r → Π x : M, TangentSpace I x} {U : Set M} {hY : IsQuotientFrameOn D Y U}
    {hU : IsOpen U}
    (he : hY.pretrivialization hU ∈ (hD.quotientPrebundle hr).pretrivializationAtlas)
    {p : TotalSpace (Fin r → 𝕜) fun x ↦ TangentSpace I x ⧸ D x} (hp : p.proj ∈ U) :
    letI := (hD.quotientPrebundle hr).totalSpaceTopology
    (hD.quotientPrebundle hr).trivializationOfMemPretrivializationAtlas he p =
      (p.proj, (hY.basis hp).equivFun p.snd) :=
  have := TangentBundle.contMDiffVectorBundle (n := n) (I := I) (M := M)
  have hV := hD.hasLocalContMDiffSubbundleFrames
  hV.trivializationOfMemPretrivializationAtlas_quotientPrebundle_apply (by simpa using hr) he hp

/-- **The quotient map `TM → TM ⧸ D` is `C^n`.** -/
theorem contMDiff_totalSpace_mkQ :
    letI := (hD.quotientPrebundle hr).totalSpaceTopology
    letI := (hD.quotientPrebundle hr).toFiberBundle
    ContMDiff (I.prod 𝓘(𝕜, E)) (I.prod 𝓘(𝕜, Fin r → 𝕜)) n
      (fun v : TangentBundle I M ↦
        (⟨v.proj, Submodule.Quotient.mk v.snd⟩ : TotalSpace (Fin r → 𝕜)
          fun x ↦ TangentSpace I x ⧸ D x)) :=
  have := TangentBundle.contMDiffVectorBundle (n := n) (I := I) (M := M)
  hD.hasLocalContMDiffSubbundleFrames.contMDiff_totalSpace_mkQ (by simpa using hr)

/-- **Sections of `TM ⧸ D` lift locally to vector fields.** A `C^n` section of `TM ⧸ D` on an
open set `W` is, near every point of `W`, the class of a `C^n` vector field. -/
theorem exists_contMDiffOn_mk_eq {W : Set M} (hW : IsOpen W)
    {s : Π x : M, TangentSpace I x ⧸ D x}
    (hs : letI := (hD.quotientPrebundle hr).totalSpaceTopology
      letI := (hD.quotientPrebundle hr).toFiberBundle
      ContMDiffOn I (I.prod 𝓘(𝕜, Fin r → 𝕜)) n
        (fun x ↦ TotalSpace.mk' (Fin r → 𝕜) (E := fun x ↦ TangentSpace I x ⧸ D x) x (s x)) W)
    {x₀ : M} (hx₀ : x₀ ∈ W) :
    ∃ U : Set M, IsOpen U ∧ x₀ ∈ U ∧ U ⊆ W ∧ ∃ σ : (Π x : M, TangentSpace I x),
      CMDiff[U] n (T% σ) ∧ ∀ x ∈ U, Submodule.Quotient.mk (σ x) = s x :=
  have := TangentBundle.contMDiffVectorBundle (n := n) (I := I) (M := M)
  hD.hasLocalContMDiffSubbundleFrames.exists_contMDiffOn_mk_eq (by simpa using hr) hW hs hx₀

/-! ### Maps of quotient bundles induced by differentials -/

section Map

variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] [FiniteDimensional 𝕜 E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners 𝕜 E' H'}
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M'] [IsManifold I' 1 M']
  [IsManifold I' (n + 1) M'] {k' r' : ℕ} {D' : Π y : M', Submodule 𝕜 (TangentSpace I' y)}
  (hD' : IsContMDiffDistribution I' n k' D') (hr' : k' + r' = finrank 𝕜 E')

/-- **Maps of quotient bundles induced by differentials.** If a `C^(n+1)` map `f : M → M'` has
differential carrying each `D x` into `D' (f x)`, then the induced map
`TM ⧸ D → TM' ⧸ D'`, `(x, [v]) ↦ (f x, [df_x v])`, is `C^n`. -/
theorem contMDiff_totalSpace_mapQ_mfderiv {f : M → M'} (hf : ContMDiff I I' (n + 1) f)
    (hfD : ∀ x, D x ≤ (D' (f x)).comap (mfderiv I I' f x).toLinearMap) :
    letI := (hD.quotientPrebundle hr).totalSpaceTopology
    letI := (hD.quotientPrebundle hr).toFiberBundle
    letI := (hD'.quotientPrebundle hr').totalSpaceTopology
    letI := (hD'.quotientPrebundle hr').toFiberBundle
    ContMDiff (I.prod 𝓘(𝕜, Fin r → 𝕜)) (I'.prod 𝓘(𝕜, Fin r' → 𝕜)) n
      (fun p : TotalSpace (Fin r → 𝕜) (fun x ↦ TangentSpace I x ⧸ D x) ↦
        (⟨f p.proj, (D p.proj).mapQ (D' (f p.proj)) (mfderiv I I' f p.proj).toLinearMap
          (hfD p.proj) p.snd⟩ : TotalSpace (Fin r' → 𝕜) fun y ↦ TangentSpace I' y ⧸ D' y)) :=
  have := TangentBundle.contMDiffVectorBundle (n := n) (I := I) (M := M)
  have := TangentBundle.contMDiffVectorBundle (n := n) (I := I') (M := M')
  hD.hasLocalContMDiffSubbundleFrames.contMDiff_totalSpace_mapQ (by simpa using hr)
    hD'.hasLocalContMDiffSubbundleFrames (by simpa using hr')
    (fun x ↦ (mfderiv I I' f x).toLinearMap) hfD (hf.contMDiff_tangentMap le_rfl)

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E] [IsManifold I 1 M] [IsManifold I (n + 1) M]
  [FiniteDimensional 𝕜 E'] [IsManifold I' 1 M'] [IsManifold I' (n + 1) M'] in
/-- If the tangent map of `g` undoes that of `f`, then the maps of quotients induced by `dg` undo
those induced by `df`. -/
private theorem mapQ_mfderiv_mapQ_mfderiv {f : M → M'} {g : M' → M}
    (hfg : ∀ z, tangentMap I' I g (tangentMap I I' f z) = z)
    (h₁ : ∀ x, D x ≤ (D' (f x)).comap (mfderiv I I' f x).toLinearMap)
    (h₂ : ∀ y, D' y ≤ (D (g y)).comap (mfderiv I' I g y).toLinearMap)
    (p : TotalSpace (Fin r → 𝕜) fun x ↦ TangentSpace I x ⧸ D x) :
    (⟨g (f p.proj), (D' (f p.proj)).mapQ (D (g (f p.proj))) (mfderiv I' I g (f p.proj)).toLinearMap
        (h₂ _) ((D p.proj).mapQ (D' (f p.proj)) (mfderiv I I' f p.proj).toLinearMap (h₁ _) p.snd)⟩ :
      TotalSpace (Fin r → 𝕜) fun x ↦ TangentSpace I x ⧸ D x) = p := by
  obtain ⟨x, a⟩ := p
  induction a using Submodule.Quotient.induction_on with
  | H v =>
    simp only [Submodule.mapQ_apply]
    -- Take classes modulo `D` in `tangentMap g (tangentMap f (x, v)) = (x, v)`.
    exact congrArg (fun w : TangentBundle I M ↦ (⟨w.proj, Submodule.Quotient.mk w.snd⟩ :
      TotalSpace (Fin r → 𝕜) fun x ↦ TangentSpace I x ⧸ D x)) (hfg ⟨x, v⟩)

/-- **The bundle isomorphism of quotient bundles induced by a diffeomorphism.** A `C^(n+1)`
diffeomorphism `Φ : M → M'` whose differential carries `D` onto `D'`, in the sense that
`v ∈ D x ↔ dΦ_x v ∈ D' (Φ x)`, induces the `C^n` diffeomorphism
`TM ⧸ D ≃ TM' ⧸ D'`, `(x, [v]) ↦ (Φ x, [dΦ_x v])`, covering `Φ` and linear on each fibre. Its
inverse is the map induced by `Φ⁻¹`. -/
def quotientDiffeomorph (Φ : M ≃ₘ^(n + 1)⟮I, I'⟯ M')
    (hΦD : ∀ x v, v ∈ D x ↔ mfderiv I I' Φ x v ∈ D' (Φ x)) :
    letI := (hD.quotientPrebundle hr).totalSpaceTopology
    letI := (hD.quotientPrebundle hr).toFiberBundle
    letI := (hD'.quotientPrebundle hr').totalSpaceTopology
    letI := (hD'.quotientPrebundle hr').toFiberBundle
    TotalSpace (Fin r → 𝕜) (fun x ↦ TangentSpace I x ⧸ D x) ≃ₘ^n⟮I.prod 𝓘(𝕜, Fin r → 𝕜),
      I'.prod 𝓘(𝕜, Fin r' → 𝕜)⟯ TotalSpace (Fin r' → 𝕜) (fun y ↦ TangentSpace I' y ⧸ D' y) :=
  letI := (hD.quotientPrebundle hr).totalSpaceTopology
  letI := (hD.quotientPrebundle hr).toFiberBundle
  letI := (hD'.quotientPrebundle hr').totalSpaceTopology
  letI := (hD'.quotientPrebundle hr').toFiberBundle
  have hn : n + 1 ≠ 0 := by simp
  have hΦD' := Φ.mem_iff_mfderiv_symm_apply_mem hn hΦD
  { toFun p := ⟨Φ p.proj, (D p.proj).mapQ (D' (Φ p.proj)) (mfderiv I I' Φ p.proj).toLinearMap
      (fun v hv ↦ (hΦD _ v).1 hv) p.snd⟩
    invFun p := ⟨Φ.symm p.proj, (D' p.proj).mapQ (D (Φ.symm p.proj))
      (mfderiv I' I Φ.symm p.proj).toLinearMap (fun w hw ↦ (hΦD' _ w).1 hw) p.snd⟩
    left_inv := mapQ_mfderiv_mapQ_mfderiv (Φ.tangentMap_symm_apply hn)
      (fun x v hv ↦ (hΦD x v).1 hv) fun y w hw ↦ (hΦD' y w).1 hw
    right_inv := mapQ_mfderiv_mapQ_mfderiv (Φ.tangentMap_apply_symm hn)
      (fun y w hw ↦ (hΦD' y w).1 hw) fun x v hv ↦ (hΦD x v).1 hv
    contMDiff_toFun := hD.contMDiff_totalSpace_mapQ_mfderiv hr hD' hr' Φ.contMDiff
      fun x v hv ↦ (hΦD x v).1 hv
    contMDiff_invFun := hD'.contMDiff_totalSpace_mapQ_mfderiv hr' hD hr Φ.symm.contMDiff
      fun y w hw ↦ (hΦD' y w).1 hw }

section quotientDiffeomorph

variable (Φ : M ≃ₘ^(n + 1)⟮I, I'⟯ M') (hΦD : ∀ x v, v ∈ D x ↔ mfderiv I I' Φ x v ∈ D' (Φ x))

/-- The bundle isomorphism induced by `Φ` sends the class of `v` over `x` to the class of
`dΦ_x v` over `Φ x`. -/
theorem quotientDiffeomorph_apply (p : TotalSpace (Fin r → 𝕜) fun x ↦ TangentSpace I x ⧸ D x) :
    letI := (hD.quotientPrebundle hr).totalSpaceTopology
    letI := (hD.quotientPrebundle hr).toFiberBundle
    letI := (hD'.quotientPrebundle hr').totalSpaceTopology
    letI := (hD'.quotientPrebundle hr').toFiberBundle
    hD.quotientDiffeomorph hr hD' hr' Φ hΦD p =
      ⟨Φ p.proj, (D p.proj).mapQ (D' (Φ p.proj)) (mfderiv I I' Φ p.proj).toLinearMap
        (fun v hv ↦ (hΦD _ v).1 hv) p.snd⟩ :=
  (rfl)

/-- The bundle isomorphism induced by `Φ` covers `Φ`. -/
@[simp]
theorem proj_quotientDiffeomorph (p : TotalSpace (Fin r → 𝕜) fun x ↦ TangentSpace I x ⧸ D x) :
    letI := (hD.quotientPrebundle hr).totalSpaceTopology
    letI := (hD.quotientPrebundle hr).toFiberBundle
    letI := (hD'.quotientPrebundle hr').totalSpaceTopology
    letI := (hD'.quotientPrebundle hr').toFiberBundle
    (hD.quotientDiffeomorph hr hD' hr' Φ hΦD p).proj = Φ p.proj :=
  (rfl)

/-- The inverse of the bundle isomorphism induced by `Φ` sends the class of `w` over `y` to the
class of `dΦ⁻¹_y w` over `Φ⁻¹ y`. -/
theorem quotientDiffeomorph_symm_apply
    (q : TotalSpace (Fin r' → 𝕜) fun y ↦ TangentSpace I' y ⧸ D' y) :
    letI := (hD.quotientPrebundle hr).totalSpaceTopology
    letI := (hD.quotientPrebundle hr).toFiberBundle
    letI := (hD'.quotientPrebundle hr').totalSpaceTopology
    letI := (hD'.quotientPrebundle hr').toFiberBundle
    (hD.quotientDiffeomorph hr hD' hr' Φ hΦD).symm q =
      ⟨Φ.symm q.proj, (D' q.proj).mapQ (D (Φ.symm q.proj))
        (mfderiv I' I Φ.symm q.proj).toLinearMap
        (fun w hw ↦ (Φ.mem_iff_mfderiv_symm_apply_mem (by simp) hΦD _ w).1 hw) q.snd⟩ :=
  (rfl)

/-- The inverse of the bundle isomorphism induced by `Φ` covers `Φ⁻¹`. -/
theorem proj_quotientDiffeomorph_symm
    (q : TotalSpace (Fin r' → 𝕜) fun y ↦ TangentSpace I' y ⧸ D' y) :
    letI := (hD.quotientPrebundle hr).totalSpaceTopology
    letI := (hD.quotientPrebundle hr).toFiberBundle
    letI := (hD'.quotientPrebundle hr').totalSpaceTopology
    letI := (hD'.quotientPrebundle hr').toFiberBundle
    ((hD.quotientDiffeomorph hr hD' hr' Φ hΦD).symm q).proj = Φ.symm q.proj :=
  (rfl)

/-- The inverse of the bundle isomorphism induced by `Φ` is the bundle isomorphism induced by
`Φ⁻¹`. -/
@[simp]
theorem quotientDiffeomorph_symm :
    letI := (hD.quotientPrebundle hr).totalSpaceTopology
    letI := (hD.quotientPrebundle hr).toFiberBundle
    letI := (hD'.quotientPrebundle hr').totalSpaceTopology
    letI := (hD'.quotientPrebundle hr').toFiberBundle
    (hD.quotientDiffeomorph hr hD' hr' Φ hΦD).symm =
      hD'.quotientDiffeomorph hr' hD hr Φ.symm (Φ.mem_iff_mfderiv_symm_apply_mem (by simp) hΦD) :=
  (rfl)

/-- The bundle isomorphism induced by `Φ` sends the class of `v` over `x` to the class of
`dΦ_x v` over `Φ x`. -/
@[simp]
theorem quotientDiffeomorph_mk (x : M) (v : TangentSpace I x) :
    letI := (hD.quotientPrebundle hr).totalSpaceTopology
    letI := (hD.quotientPrebundle hr).toFiberBundle
    letI := (hD'.quotientPrebundle hr').totalSpaceTopology
    letI := (hD'.quotientPrebundle hr').toFiberBundle
    hD.quotientDiffeomorph hr hD' hr' Φ hΦD ⟨x, Submodule.Quotient.mk v⟩ =
      ⟨Φ x, Submodule.Quotient.mk (mfderiv I I' Φ x v)⟩ :=
  (rfl)

/-- The inverse of the bundle isomorphism induced by `Φ` is induced by `Φ⁻¹`: it sends the class
of `w` over `y` to the class of `dΦ⁻¹_y w` over `Φ⁻¹ y`. -/
theorem quotientDiffeomorph_symm_mk (y : M') (w : TangentSpace I' y) :
    letI := (hD.quotientPrebundle hr).totalSpaceTopology
    letI := (hD.quotientPrebundle hr).toFiberBundle
    letI := (hD'.quotientPrebundle hr').totalSpaceTopology
    letI := (hD'.quotientPrebundle hr').toFiberBundle
    (hD.quotientDiffeomorph hr hD' hr' Φ hΦD).symm ⟨y, Submodule.Quotient.mk w⟩ =
      ⟨Φ.symm y, Submodule.Quotient.mk (mfderiv I' I Φ.symm y w)⟩ :=
  (rfl)

/-- The fibre maps of the bundle isomorphism induced by `Φ` are the isomorphisms
`T_x M ⧸ D x ≃ T_(Φ x) M' ⧸ D' (Φ x)` of normal spaces induced by `dΦ_x`
(`IsLocalDiffeomorphAt.mfderivQuotientEquiv`). -/
theorem quotientDiffeomorph_mk_eq_mfderivQuotientEquiv (x : M) (a : TangentSpace I x ⧸ D x) :
    letI := (hD.quotientPrebundle hr).totalSpaceTopology
    letI := (hD.quotientPrebundle hr).toFiberBundle
    letI := (hD'.quotientPrebundle hr').totalSpaceTopology
    letI := (hD'.quotientPrebundle hr').toFiberBundle
    hD.quotientDiffeomorph hr hD' hr' Φ hΦD ⟨x, a⟩ =
      ⟨Φ x, (Φ.isLocalDiffeomorph x).mfderivQuotientEquiv (by simp)
        (Submodule.ext fun v ↦ hΦD x v) a⟩ := by
  induction a using Submodule.Quotient.induction_on with
  | H v => rw [quotientDiffeomorph_mk, IsLocalDiffeomorphAt.mfderivQuotientEquiv_mk]

end quotientDiffeomorph

/-- The identity of `M` induces the identity of `TM ⧸ D`. -/
@[simp]
theorem quotientDiffeomorph_refl (h : ∀ x v, v ∈ D x ↔
      mfderiv I I (Diffeomorph.refl I M (n + 1)) x v ∈ D (Diffeomorph.refl I M (n + 1) x)) :
    letI := (hD.quotientPrebundle hr).totalSpaceTopology
    letI := (hD.quotientPrebundle hr).toFiberBundle
    hD.quotientDiffeomorph hr hD hr (Diffeomorph.refl I M (n + 1)) h = Diffeomorph.refl _ _ _ := by
  let := (hD.quotientPrebundle hr).totalSpaceTopology
  let := (hD.quotientPrebundle hr).toFiberBundle
  refine Diffeomorph.ext fun ⟨x, a⟩ ↦ ?_
  induction a using Submodule.Quotient.induction_on with
  | H v =>
    rw [quotientDiffeomorph_mk, Diffeomorph.coe_refl, Diffeomorph.coe_refl, mfderiv_id,
      ContinuousLinearMap.id_apply, id_eq, id_eq]

/-- **Functoriality.** The bundle isomorphism induced by a composite of diffeomorphisms is the
composite of the induced bundle isomorphisms. -/
theorem quotientDiffeomorph_trans {E'' : Type*} [NormedAddCommGroup E''] [NormedSpace 𝕜 E'']
    [FiniteDimensional 𝕜 E''] {H'' : Type*} [TopologicalSpace H'']
    {I'' : ModelWithCorners 𝕜 E'' H''} {M'' : Type*} [TopologicalSpace M'']
    [ChartedSpace H'' M''] [IsManifold I'' 1 M''] [IsManifold I'' (n + 1) M''] {k'' r'' : ℕ}
    {D'' : Π z : M'', Submodule 𝕜 (TangentSpace I'' z)}
    (hD'' : IsContMDiffDistribution I'' n k'' D'') (hr'' : k'' + r'' = finrank 𝕜 E'')
    (Φ : M ≃ₘ^(n + 1)⟮I, I'⟯ M') (Ψ : M' ≃ₘ^(n + 1)⟮I', I''⟯ M'')
    (hΦD : ∀ x v, v ∈ D x ↔ mfderiv I I' Φ x v ∈ D' (Φ x))
    (hΨD : ∀ y w, w ∈ D' y ↔ mfderiv I' I'' Ψ y w ∈ D'' (Ψ y)) :
    letI := (hD.quotientPrebundle hr).totalSpaceTopology
    letI := (hD.quotientPrebundle hr).toFiberBundle
    letI := (hD'.quotientPrebundle hr').totalSpaceTopology
    letI := (hD'.quotientPrebundle hr').toFiberBundle
    letI := (hD''.quotientPrebundle hr'').totalSpaceTopology
    letI := (hD''.quotientPrebundle hr'').toFiberBundle
    hD.quotientDiffeomorph hr hD'' hr'' (Φ.trans Ψ)
        (Φ.mem_iff_mfderiv_trans_apply_mem Ψ (by simp) hΦD hΨD) =
      (hD.quotientDiffeomorph hr hD' hr' Φ hΦD).trans
        (hD'.quotientDiffeomorph hr' hD'' hr'' Ψ hΨD) := by
  let := (hD.quotientPrebundle hr).totalSpaceTopology
  let := (hD.quotientPrebundle hr).toFiberBundle
  let := (hD'.quotientPrebundle hr').totalSpaceTopology
  let := (hD'.quotientPrebundle hr').toFiberBundle
  let := (hD''.quotientPrebundle hr'').totalSpaceTopology
  let := (hD''.quotientPrebundle hr'').toFiberBundle
  refine Diffeomorph.ext fun ⟨x, a⟩ ↦ ?_
  induction a using Submodule.Quotient.induction_on with
  | H v =>
    rw [Diffeomorph.coe_trans, Function.comp_apply, quotientDiffeomorph_mk, quotientDiffeomorph_mk,
      quotientDiffeomorph_mk, Diffeomorph.coe_trans,
      mfderiv_comp_apply x (Ψ.mdifferentiable (by simp) (Φ x)) (Φ.mdifferentiable (by simp) x),
      Function.comp_apply]

end Map

end TauCeti.IsContMDiffDistribution
