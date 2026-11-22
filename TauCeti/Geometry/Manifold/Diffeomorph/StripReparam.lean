/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Diffeomorph

/-!
# Reparametrizing a self-map of `M × M` along its strips

Let `U ⊆ M` be open. A self-map `F` of `M × M` **preserves the strip leaves over `U`**
(`TauCeti.PreservesStripLeaves U F`) when it maps every horizontal leaf `M × {w}` with `w ∈ U`
and every vertical leaf `{z} × M` with `z ∈ U` into itself. On the two strips `M × U` and
`U × M` such a map has the form

`F (z, w) = (φ (z, w), w)` for `w ∈ U`, and `F (z, w) = (z, θ (z, w))` for `z ∈ U`,

so it is the identity on `U × U`, and on each strip it is a family of maps of the leaves
parametrized by the points of `U`. Leaf-preserving maps contain the identity and are closed under
composition (`TauCeti.preservesStripLeaves_id`, `TauCeti.PreservesStripLeaves.comp`).

Given a self-map `ρ` of `M`, the **strip reparametrization** `TauCeti.stripReparam U ρ F`
replaces the parameter of these two families by its image under `ρ`:

`(z, w) ↦ (φ (z, ρ w), w)` for `w ∈ U`, `(z, w) ↦ (z, θ (ρ z, w))` for `z ∈ U`,

and agrees with `F` on the rest of `M × M`. The two formulas agree on `U × U`, where both are the
identity (`TauCeti.stripReparam_of_mem_right`, `TauCeti.stripReparam_of_mem_left`). For an
arbitrary `F`, the three branches of the definition are `TauCeti.stripReparam_of_mem_right`,
`TauCeti.stripReparam_of_mem_of_notMem` and `TauCeti.stripReparam_of_notMem`. The result
again preserves the strip leaves (`TauCeti.PreservesStripLeaves.stripReparam`), it is `F` itself
for `ρ = id` (`TauCeti.stripReparam_id`), and it agrees with `F` wherever `ρ` fixes both
coordinates (`TauCeti.stripReparam_of_apply_eq`). If `ρ` collapses a set `D ⊆ U` to a point `c`
and `F` fixes the two leaves through `c` pointwise, the reparametrization is the identity on
`(D × M) ∪ (M × D)` (`TauCeti.stripReparam_of_mem_left_of_mem`,
`TauCeti.stripReparam_of_mem_right_of_mem`).

When `ρ` maps `U` into itself, reparametrization is compatible with composition
(`TauCeti.stripReparam_comp`), provided the inner map does not move points of `Uᶜ × Uᶜ` into the
strips, which holds for an inverse of a leaf-preserving map
(`TauCeti.PreservesStripLeaves.mapsTo_compl_prod_of_leftInverse`); the reparametrization of the
identity is the identity (`TauCeti.stripReparam_id_right`). So the reparametrizations of a
bijection and of its inverse are mutually inverse (`TauCeti.leftInverse_stripReparam`).

**Smoothness.** If `F` is `C^n`, and `ρ` is `C^n` and fixes every point outside a closed subset
`K` of `U`, then the reparametrization is `C^n` (`ContMDiff.stripReparam`). Near a point of a strip
it is given by one of the two formulas, which are smooth there, and near a point of `Uᶜ × Uᶜ` it
agrees with `F`, since `ρ` fixes both coordinates nearby. The same holds for a family `ρ p`
depending jointly `C^n`-smoothly on a parameter `p` (`TauCeti.contMDiff_stripReparam`). Hence,
for `ρ` mapping `U` into itself, a `C^n` diffeomorphism whose inverse also preserves the strip
leaves has a reparametrization which is again a `C^n` diffeomorphism, with inverse the
reparametrization of the inverse (`Diffeomorph.stripReparam`). The diffeotopy of `M × M` given
by a family `ρ t`, `t ∈ [0, 1]`, starting at `ρ 0 = id`, is in
`TauCeti.Geometry.Diffeomorphism.Diffeotopy.StripReparam`.

This is the relative adjustment in Gromov's recognition of the standard symplectic `ℝ⁴` among
symplectic `4`-manifolds standard at infinity. There `M = S²`, `F` is the diffeomorphism of
`S² × S²` built from the two families of holomorphic spheres, normalized on the strips around the
two cap spheres `S² × {∞}` and `{∞} × S²`, `U` and `D ⊆ U` are concentric discs about `∞`, and `ρ`
is a radial map collapsing `D` to `∞`, read through a disc chart (`TauCeti.radialRescale` and
`TauCeti.chartExtend`). The reparametrized diffeomorphism is the identity near the two cap
spheres, so that it can be compared with the given identification at infinity.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  AMS Colloquium Publications 52, 2012, proof of Theorem 9.4.7 (ii).
-/

public section

open Set Function Topology
open scoped Manifold ContDiff

namespace TauCeti

section Leaves

variable {M : Type*} {U : Set M} {F G : M × M → M × M} {ρ : M → M} {z w : M}

/-- A self-map `F` of `M × M` **preserves the strip leaves over `U`** when it maps every
horizontal leaf `M × {w}` with `w ∈ U`, and every vertical leaf `{z} × M` with `z ∈ U`, into
itself. In particular it is the identity on `U × U`. -/
structure PreservesStripLeaves (U : Set M) (F : M × M → M × M) : Prop where
  /-- Each horizontal leaf `M × {w}` over a point `w ∈ U` is mapped into itself. -/
  snd_apply_of_mem : ∀ z, ∀ w ∈ U, (F (z, w)).2 = w
  /-- Each vertical leaf `{z} × M` over a point `z ∈ U` is mapped into itself. -/
  fst_apply_of_mem : ∀ z ∈ U, ∀ w, (F (z, w)).1 = z

/-- The identity preserves the strip leaves. -/
theorem preservesStripLeaves_id : PreservesStripLeaves U (id : M × M → M × M) :=
  ⟨fun _ _ _ ↦ rfl, fun _ _ _ ↦ rfl⟩

namespace PreservesStripLeaves

/-- A map preserving the strip leaves is the identity on `U × U`. -/
theorem apply_of_mem_of_mem (hF : PreservesStripLeaves U F) (hz : z ∈ U) (hw : w ∈ U) :
    F (z, w) = (z, w) :=
  Prod.ext (hF.fst_apply_of_mem z hz w) (hF.snd_apply_of_mem z w hw)

/-- On the horizontal strip `M × U`, a map preserving the strip leaves keeps the second
coordinate. -/
theorem apply_of_mem_right (hF : PreservesStripLeaves U F) (hw : w ∈ U) :
    F (z, w) = ((F (z, w)).1, w) :=
  Prod.ext rfl (hF.snd_apply_of_mem z w hw)

/-- On the vertical strip `U × M`, a map preserving the strip leaves keeps the first
coordinate. -/
theorem apply_of_mem_left (hF : PreservesStripLeaves U F) (hz : z ∈ U) :
    F (z, w) = (z, (F (z, w)).2) :=
  Prod.ext (hF.fst_apply_of_mem z hz w) rfl

/-- Maps preserving the strip leaves are closed under composition. -/
theorem comp (hF : PreservesStripLeaves U F) (hG : PreservesStripLeaves U G) :
    PreservesStripLeaves U (F ∘ G) where
  snd_apply_of_mem z w hw := by
    rw [comp_apply, hG.apply_of_mem_right hw, hF.snd_apply_of_mem _ _ hw]
  fst_apply_of_mem z hz w := by
    rw [comp_apply, hG.apply_of_mem_left hz, hF.fst_apply_of_mem _ hz]

/-- A right inverse `G` of a map `F` preserving the strip leaves maps `Uᶜ × Uᶜ` into itself: a
point of a strip is mapped by `F` into the same strip. -/
theorem mapsTo_compl_prod_of_leftInverse (hF : PreservesStripLeaves U F) (hFG : LeftInverse F G) :
    MapsTo G (Uᶜ ×ˢ Uᶜ) (Uᶜ ×ˢ Uᶜ) := by
  rintro ⟨z, w⟩ ⟨hz, hw⟩
  refine ⟨fun h ↦ hz ?_, fun h ↦ hw ?_⟩
  · have := hF.fst_apply_of_mem _ h (G (z, w)).2
    rw [Prod.mk.eta, hFG] at this
    exact this ▸ h
  · have := hF.snd_apply_of_mem (G (z, w)).1 _ h
    rw [Prod.mk.eta, hFG] at this
    exact this ▸ h

end PreservesStripLeaves

open scoped Classical in
/-- The **strip reparametrization** of a self-map `F` of `M × M` by a self-map `ρ` of `M`. On the
horizontal strip `M × U` it is `(z, w) ↦ ((F (z, ρ w)).1, w)`, on the rest of the vertical strip
`U × M` it is `(z, w) ↦ (z, (F (ρ z, w)).2)`, and elsewhere it is `F`. It is intended for maps `F`
preserving the strip leaves over `U` (`TauCeti.PreservesStripLeaves`): then the two formulas agree
on `U × U`, where both are the identity, and the families of leaf maps of `F` over the strips are
reparametrized by `ρ`. -/
noncomputable def stripReparam (U : Set M) (ρ : M → M) (F : M × M → M × M) (x : M × M) :
    M × M :=
  if x.2 ∈ U then ((F (x.1, ρ x.2)).1, x.2)
  else if x.1 ∈ U then (x.1, (F (ρ x.1, x.2)).2) else F x

/-- On the horizontal strip `M × U`, the reparametrization reads the horizontal leaf map of `F`
over `ρ w`. -/
theorem stripReparam_of_mem_right (hw : w ∈ U) :
    stripReparam U ρ F (z, w) = ((F (z, ρ w)).1, w) := by
  simp [stripReparam, hw]

/-- On the part `U × Uᶜ` of the vertical strip off the horizontal strip, the reparametrization
reads the vertical leaf map of `F` over `ρ z`, for an arbitrary `F`. -/
theorem stripReparam_of_mem_of_notMem (hz : z ∈ U) (hw : w ∉ U) :
    stripReparam U ρ F (z, w) = (z, (F (ρ z, w)).2) := by
  simp [stripReparam, hw, hz]

/-- On the vertical strip `U × M`, the reparametrization reads the vertical leaf map of `F` over
`ρ z`. -/
theorem stripReparam_of_mem_left (hF : PreservesStripLeaves U F) (hz : z ∈ U) :
    stripReparam U ρ F (z, w) = (z, (F (ρ z, w)).2) := by
  by_cases hw : w ∈ U
  · rw [stripReparam_of_mem_right hw, hF.fst_apply_of_mem _ hz,
      hF.snd_apply_of_mem _ _ hw]
  · exact stripReparam_of_mem_of_notMem hz hw

/-- Off the two strips, the reparametrization is `F`. -/
theorem stripReparam_of_notMem (hz : z ∉ U) (hw : w ∉ U) :
    stripReparam U ρ F (z, w) = F (z, w) := by
  simp [stripReparam, hz, hw]

/-- The reparametrization agrees with `F` at every point both of whose coordinates `ρ` fixes. -/
theorem stripReparam_of_apply_eq (hF : PreservesStripLeaves U F) (hz : ρ z = z) (hw : ρ w = w) :
    stripReparam U ρ F (z, w) = F (z, w) := by
  by_cases hwU : w ∈ U
  · rw [stripReparam_of_mem_right hwU, hw, ← hF.apply_of_mem_right hwU]
  · by_cases hzU : z ∈ U
    · rw [stripReparam_of_mem_left hF hzU, hz, ← hF.apply_of_mem_left hzU]
    · exact stripReparam_of_notMem hzU hwU

/-- The reparametrization by the identity is `F` itself. -/
@[simp]
theorem stripReparam_id (hF : PreservesStripLeaves U F) : stripReparam U id F = F := by
  ext1 ⟨z, w⟩
  exact stripReparam_of_apply_eq hF rfl rfl

/-- The reparametrization of the identity is the identity. -/
@[simp]
theorem stripReparam_id_right : stripReparam U ρ (id : M × M → M × M) = id := by
  ext1 ⟨z, w⟩
  by_cases hw : w ∈ U
  · simp [stripReparam, hw]
  · by_cases hz : z ∈ U <;> simp [stripReparam, hw, hz]

/-- The strip reparametrization of a map preserving the strip leaves preserves the strip
leaves. -/
theorem PreservesStripLeaves.stripReparam (hF : PreservesStripLeaves U F) :
    PreservesStripLeaves U (stripReparam U ρ F) where
  snd_apply_of_mem z w hw := by rw [stripReparam_of_mem_right hw]
  fst_apply_of_mem z hz w := by rw [stripReparam_of_mem_left hF hz]

/-- If `ρ` collapses a subset `D ⊆ U` to a point `c` and `F` fixes the horizontal leaf
`M × {c}` pointwise, then the reparametrization is the identity on `M × D`. -/
theorem stripReparam_of_mem_right_of_mem {D : Set M} {c : M} (hDU : D ⊆ U)
    (hρD : ∀ x ∈ D, ρ x = c) (hFc : ∀ x, F (x, c) = (x, c)) (hw : w ∈ D) :
    stripReparam U ρ F (z, w) = (z, w) := by
  rw [stripReparam_of_mem_right (hDU hw), hρD w hw, hFc]

/-- If `ρ` collapses a subset `D ⊆ U` to a point `c`, and `F` preserves the strip leaves and fixes
the vertical leaf `{c} × M` pointwise, then the reparametrization is the identity on `D × M`. -/
theorem stripReparam_of_mem_left_of_mem {D : Set M} {c : M} (hF : PreservesStripLeaves U F)
    (hDU : D ⊆ U) (hρD : ∀ x ∈ D, ρ x = c) (hFc : ∀ x, F (c, x) = (c, x))
    (hz : z ∈ D) : stripReparam U ρ F (z, w) = (z, w) := by
  rw [stripReparam_of_mem_left hF (hDU hz), hρD z hz, hFc]

/-- **Strip reparametrization is compatible with composition**, for maps preserving the strip
leaves and a map `ρ` sending `U` into itself, provided the inner map sends `Uᶜ × Uᶜ` into
itself. -/
theorem stripReparam_comp (hF : PreservesStripLeaves U F) (hG : PreservesStripLeaves U G)
    (hρ : MapsTo ρ U U) (hGc : MapsTo G (Uᶜ ×ˢ Uᶜ) (Uᶜ ×ˢ Uᶜ)) :
    stripReparam U ρ (F ∘ G) = stripReparam U ρ F ∘ stripReparam U ρ G := by
  ext1 ⟨z, w⟩
  by_cases hw : w ∈ U
  · rw [comp_apply, stripReparam_of_mem_right hw, stripReparam_of_mem_right hw,
      stripReparam_of_mem_right hw, comp_apply, hG.apply_of_mem_right (hρ hw)]
  by_cases hz : z ∈ U
  · rw [comp_apply, stripReparam_of_mem_left (hF.comp hG) hz, stripReparam_of_mem_left hG hz,
      stripReparam_of_mem_left hF hz, comp_apply, hG.apply_of_mem_left (hρ hz)]
  · obtain ⟨hz', hw'⟩ := hGc (mk_mem_prod hz hw)
    rw [comp_apply, stripReparam_of_notMem hz hw, stripReparam_of_notMem hz hw, comp_apply,
      ← Prod.mk.eta (p := G (z, w)), stripReparam_of_notMem hz' hw']

/-- Let `F` and a right inverse `G` of `F` both preserve the strip leaves, and let `ρ` map `U` into
itself. Then the reparametrization of `G` is a right inverse of the reparametrization of `F`. -/
theorem leftInverse_stripReparam (hF : PreservesStripLeaves U F) (hG : PreservesStripLeaves U G)
    (hρ : MapsTo ρ U U) (hFG : LeftInverse F G) :
    LeftInverse (stripReparam U ρ F) (stripReparam U ρ G) := by
  intro x
  rw [← comp_apply (f := stripReparam U ρ F), ← stripReparam_comp hF hG hρ
    (hF.mapsTo_compl_prod_of_leftInverse hFG), hFG.comp_eq_id, stripReparam_id_right, id]

end Leaves

/-! ### Smoothness -/

section Smooth

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners 𝕜 E' H'}
  {P : Type*} [TopologicalSpace P] [ChartedSpace H' P] {n : ℕ∞ω}
  {U K : Set M} {F : M × M → M × M}

/-- **Smooth dependence of the strip reparametrization on parameters.** Let `U ⊆ M` be open, `F`
a `C^n` self-map of `M × M` preserving the strip leaves over `U`, and `ρ p`, for `p` in a manifold
`P`, self-maps of `M` depending jointly `C^n`-smoothly on `p` and the point, each fixing every
point outside a closed subset `K ⊆ U`. Then the reparametrizations of `F`
by the `ρ p` depend jointly `C^n`-smoothly on `p` and the point of `M × M`. -/
theorem contMDiff_stripReparam {ρ : P → M → M} (hU : IsOpen U) (hK : IsClosed K) (hKU : K ⊆ U)
    (hρ : ContMDiff (I'.prod I) I n fun q : P × M ↦ ρ q.1 q.2) (hρK : ∀ p, ∀ x ∉ K, ρ p x = x)
    (hF : ContMDiff (I.prod I) (I.prod I) n F)
    (hFU : PreservesStripLeaves U F) :
    ContMDiff (I'.prod (I.prod I)) (I.prod I) n
      fun q : P × (M × M) ↦ stripReparam U (ρ q.1) F q.2 := by
  rintro ⟨p₀, z₀, w₀⟩
  have h₁ : ContMDiff (I'.prod (I.prod I)) I n fun q : P × (M × M) ↦ q.2.1 :=
    contMDiff_fst.comp contMDiff_snd
  have h₂ : ContMDiff (I'.prod (I.prod I)) I n fun q : P × (M × M) ↦ q.2.2 :=
    contMDiff_snd.comp contMDiff_snd
  have hc₁ : Continuous fun q : P × (M × M) ↦ q.2.1 := continuous_fst.comp continuous_snd
  have hc₂ : Continuous fun q : P × (M × M) ↦ q.2.2 := continuous_snd.comp continuous_snd
  by_cases hw₀ : w₀ ∈ U
  · -- On the horizontal strip, the reparametrization is the reparametrized horizontal leaf map.
    have hs : ContMDiff (I'.prod (I.prod I)) (I.prod I) n
        fun q : P × (M × M) ↦ ((F (q.2.1, ρ q.1 q.2.2)).1, q.2.2) :=
      (contMDiff_fst.comp (hF.comp (h₁.prodMk (hρ.comp (contMDiff_fst.prodMk h₂))))).prodMk h₂
    refine (hs _).congr_of_eventuallyEq ?_
    filter_upwards [(hU.preimage hc₂).mem_nhds hw₀] with q hq
    exact stripReparam_of_mem_right hq
  by_cases hz₀ : z₀ ∈ U
  · -- On the vertical strip, the reparametrization is the reparametrized vertical leaf map.
    have hs : ContMDiff (I'.prod (I.prod I)) (I.prod I) n
        fun q : P × (M × M) ↦ (q.2.1, (F (ρ q.1 q.2.1, q.2.2)).2) :=
      h₁.prodMk (contMDiff_snd.comp (hF.comp ((hρ.comp (contMDiff_fst.prodMk h₁)).prodMk h₂)))
    refine (hs _).congr_of_eventuallyEq ?_
    filter_upwards [(hU.preimage hc₁).mem_nhds hz₀] with q hq
    exact stripReparam_of_mem_left hFU hq
  · -- Off the strips, `ρ` fixes both coordinates nearby, so the reparametrization is `F`.
    refine ((hF.comp contMDiff_snd) _).congr_of_eventuallyEq ?_
    filter_upwards [(hK.isOpen_compl.preimage hc₁).mem_nhds (fun h ↦ hz₀ (hKU h)),
      (hK.isOpen_compl.preimage hc₂).mem_nhds (fun h ↦ hw₀ (hKU h))] with q hq₁ hq₂
    exact stripReparam_of_apply_eq hFU (hρK _ _ hq₁) (hρK _ _ hq₂)

/-- **Smoothness of the strip reparametrization.** Let `U ⊆ M` be open and `F` a `C^n` self-map
of `M × M` preserving the strip leaves over `U`. If `ρ` is a `C^n` self-map of `M` fixing every
point outside a closed subset `K ⊆ U`, then the reparametrization of
`F` by `ρ` is `C^n`. -/
theorem _root_.ContMDiff.stripReparam {ρ : M → M} (hF : ContMDiff (I.prod I) (I.prod I) n F)
    (hFU : PreservesStripLeaves U F) (hU : IsOpen U) (hK : IsClosed K) (hKU : K ⊆ U)
    (hρ : ContMDiff I I n ρ) (hρK : ∀ x ∉ K, ρ x = x) :
    ContMDiff (I.prod I) (I.prod I) n (stripReparam U ρ F) :=
  (contMDiff_stripReparam (P := M × M) (I' := I.prod I) (ρ := fun _ ↦ ρ) hU hK hKU
    (hρ.comp contMDiff_snd) (fun _ ↦ hρK) hF hFU).comp
    (contMDiff_id.prodMk contMDiff_id)

end Smooth

end TauCeti

/-! ### Diffeomorphisms -/

namespace Diffeomorph

open TauCeti

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] {n : ℕ∞ω}
  {U K : Set M} {ρ : M → M}

/-- **The strip reparametrization of a diffeomorphism.** Let `U ⊆ M` be open and `F` a `C^n`
diffeomorphism of `M × M` which, together with its inverse, preserves the strip leaves over `U`.
If `ρ` is a `C^n` self-map of `M` mapping `U` into itself and fixing every point outside a closed
subset `K ⊆ U`, then the reparametrization of `F` by `ρ` is a `C^n` diffeomorphism
(`Diffeomorph.coe_stripReparam`), whose inverse is the reparametrization of `F.symm`
(`Diffeomorph.stripReparam_symm`). -/
noncomputable def stripReparam (F : (M × M) ≃ₘ^n⟮I.prod I, I.prod I⟯ (M × M))
    (hF : PreservesStripLeaves U F) (hF' : PreservesStripLeaves U F.symm) (hU : IsOpen U)
    (hK : IsClosed K) (hKU : K ⊆ U) (hρ : ContMDiff I I n ρ) (hρK : ∀ x ∉ K, ρ x = x)
    (hρU : MapsTo ρ U U) : (M × M) ≃ₘ^n⟮I.prod I, I.prod I⟯ (M × M) where
  toFun := TauCeti.stripReparam U ρ F
  invFun := TauCeti.stripReparam U ρ F.symm
  left_inv := leftInverse_stripReparam hF' hF hρU F.symm_apply_apply
  right_inv := leftInverse_stripReparam hF hF' hρU F.apply_symm_apply
  contMDiff_toFun := F.contMDiff.stripReparam hF hU hK hKU hρ hρK
  contMDiff_invFun := F.symm.contMDiff.stripReparam hF' hU hK hKU hρ hρK

variable (F : (M × M) ≃ₘ^n⟮I.prod I, I.prod I⟯ (M × M)) (hF : PreservesStripLeaves U F)
  (hF' : PreservesStripLeaves U F.symm) (hU : IsOpen U) (hK : IsClosed K) (hKU : K ⊆ U)
  (hρ : ContMDiff I I n ρ) (hρK : ∀ x ∉ K, ρ x = x) (hρU : MapsTo ρ U U)

@[simp]
theorem coe_stripReparam :
    ⇑(F.stripReparam hF hF' hU hK hKU hρ hρK hρU) = TauCeti.stripReparam U ρ F :=
  (rfl)

/-- The inverse of the strip reparametrization of a diffeomorphism is the strip
reparametrization of its inverse. -/
@[simp]
theorem stripReparam_symm :
    (F.stripReparam hF hF' hU hK hKU hρ hρK hρU).symm =
      F.symm.stripReparam hF' hF hU hK hKU hρ hρK hρU :=
  (rfl)

end Diffeomorph
