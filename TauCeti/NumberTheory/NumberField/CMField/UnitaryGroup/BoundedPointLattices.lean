/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.CMField.UnitaryGroup.PointLattice
public import TauCeti.NumberTheory.NumberField.CMField.UnitaryGroup.Support
import TauCeti.RingTheory.DedekindDomain.AdicValuation.ValuativeRel
import TauCeti.Topology.Algebra.Module.Quotient

/-!
# Point lattices cut by a subspace, under two-sided bounds

Let `V = (J, x)` be a hermitian space with an adelic frame over a CM field `E`, and for a point
`g ∈ G_f` let `Λ_g = (x_f g) Ôⁿ` be its lattice (`TauCeti.FramedHermitianSpace.finiteLattice`).
Fix a submodule `W` of `𝔸_fⁿ` over the finite adeles. For a graded space, `W` is the orthogonal
`X^⊥` of the part `X`, and `Λ_g ∩ W` is the intersection lattice `Λ⁻_g` that enters the unfolding
of Bessel periods. For `a, b ∈ 𝔸_f`, say that `g` *satisfies the bounds* if
`a (Λ_1 ∩ W) ⊆ Λ_g ∩ W` and `b (Λ_g ∩ W) ⊆ Λ_1 ∩ W`; typically `a = (star q)ᵏ` and `b = qᵏ` for a
unit `q` of `𝔸_f`.

* For units `a, b`, only finitely many lattices `Λ_g ∩ W` satisfy the bounds
  (`TauCeti.FramedHermitianSpace.finite_image_finiteLattice_inf`). More generally, finitely many
  submodules `L ⊆ W` over `Ô` satisfy `a (Λ_g ∩ W) ⊆ L` and `b L ⊆ Λ_g`
  (`TauCeti.FramedHermitianSpace.finite_setOf_le_finiteLattice_inf`): they lie in the compact set
  `b⁻¹ Λ_g` and contain the open submodule `a Λ_g ∩ W`, and only finitely many submodules do
  (`Submodule.finite_setOf_inf_le_le_subset`).
* Lattice membership is local: for the indicator `e_T` of any set `T` of finite places,
  `y ∈ Λ_g` exactly when `e_T y ∈ Λ_g` and `e_{Tᶜ} y ∈ Λ_g`, as for every submodule over `Ô`:
  `IsDedekindDomain.FiniteAdeleRing.mem_iff_indicatorOne_smul_mem_and_indicatorOne_compl_smul_mem`.
  For `T` stable under conjugation, let `g_T` be the cut of `g` along `T`
  (`TauCeti.finiteAdelicUnitaryGroup.cut`), with the components of `g` at `T` and `1` elsewhere.
  Then `e_T y ∈ Λ_{g_T}` if and only if `e_T y ∈ Λ_g`, and `e_{Tᶜ} y ∈ Λ_{g_T}` if and only if
  `e_{Tᶜ} y ∈ Λ_1`.
* Consequently, if `g` satisfies the bounds and `a`, `b` are invertible with integral inverses at
  every place outside `T`, then `Λ_{g_T} ∩ W = Λ_g ∩ W`
  (`TauCeti.FramedHermitianSpace.finiteLattice_cut_inf_eq`): away from `T` the bounds force
  `Λ_g ∩ W` to agree with `Λ_1 ∩ W`, so `Λ_g ∩ W` only depends on the components of `g` at `T`.

## References

* O. T. O'Meara, *Introduction to Quadratic Forms*, §81, for the finiteness of the lattices between
  two lattices and the local determination of a lattice.

The statements are those of `New.Grading.finite_image_latticeMinus`,
`New.Space.mem_lattice_iff_idem_smul` and `New.Grading.HasLatticeBounds.latticeMinus_componentOn`
in `src/Lib/Weil/Periods/LatticeBounds.lean` of grh-lean (L. Alpöge and L. Sernau,
https://github.com/lsernau/grh-lean, Apache 2.0), stated here for an arbitrary submodule `W` and
arbitrary scalars `a`, `b`, and with the cut of `g` along `T` in place of its component on `T`.
The finiteness follows the proof plan there: compactness of `b⁻¹ Λ_g`, discreteness of the
quotient by `a Λ_g` and the modular law.
-/

public noncomputable section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Matrix NumberField NumberField.IsCMField
open scoped NumberField.AdeleRing Pointwise

namespace TauCeti.FramedHermitianSpace

variable {E : Type*} [Field E] [NumberField E] [IsCMField E]
  {ι : Type*} [Fintype ι] [DecidableEq ι] {s : ι → ℤˣ}
  (V : FramedHermitianSpace E s)

/-! ### Finitely many lattices under the bounds -/

/-- **Finitely many submodules under the bounds.** For units `a, b` of `𝔸_f`, a submodule `W` of
`𝔸_fⁿ` over the finite adeles and a point `g`, only finitely many submodules `L ⊆ W` over `Ô`
satisfy `a (Λ_g ∩ W) ⊆ L` and `b L ⊆ Λ_g`. -/
theorem finite_setOf_le_finiteLattice_inf (W : Submodule 𝔸ᶠ[E] (ι → 𝔸ᶠ[E]))
    (g : finiteAdelicUnitaryGroup E ι) {a b : 𝔸ᶠ[E]} (ha : IsUnit a) (hb : IsUnit b) :
    {L : Submodule (FiniteAdeleRing.integralAdeles (𝓞 E) E) (ι → 𝔸ᶠ[E]) |
      L ≤ W.restrictScalars _ ∧ a • (V.finiteLattice g ⊓ W.restrictScalars _) ≤ L ∧
        b • L ≤ V.finiteLattice g}.Finite := by
  obtain ⟨a, rfl⟩ := ha
  obtain ⟨b, rfl⟩ := hb
  set F : Matrix ι ι 𝔸ᶠ[E] := ↑(V.frame.2 * g)
  set F' : Matrix ι ι 𝔸ᶠ[E] := ↑(V.frame.2 * g)⁻¹
  set O : Set (ι → 𝔸ᶠ[E]) := Set.univ.pi fun _ ↦ FiniteAdeleRing.integralAdeles (𝓞 E) E
  have hFF' (y : ι → 𝔸ᶠ[E]) : F *ᵥ (F' *ᵥ y) = y := by
    rw [mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec]
  have hinv (c : 𝔸ᶠ[E]ˣ) (y : ι → 𝔸ᶠ[E]) : (↑c⁻¹ : 𝔸ᶠ[E]) • (↑c : 𝔸ᶠ[E]) • y = y := by
    rw [smul_smul, Units.inv_mul, one_smul]
  -- `a Λ_g` is open, as the preimage of the open set `Ôⁿ` under `y ↦ F⁻¹ (a⁻¹ y)`.
  have hU : IsOpen (((a : 𝔸ᶠ[E]) • V.finiteLattice g :
      Submodule (FiniteAdeleRing.integralAdeles (𝓞 E) E) (ι → 𝔸ᶠ[E])) : Set (ι → 𝔸ᶠ[E])) := by
    have hpre : (((a : 𝔸ᶠ[E]) • V.finiteLattice g :
        Submodule (FiniteAdeleRing.integralAdeles (𝓞 E) E) (ι → 𝔸ᶠ[E])) : Set (ι → 𝔸ᶠ[E])) =
          (fun y ↦ F' *ᵥ ((↑a⁻¹ : 𝔸ᶠ[E]) • y)) ⁻¹' O := by
      ext y
      rw [SetLike.mem_coe, Submodule.mem_smul_pointwise_iff_exists, Set.mem_preimage,
        Set.mem_univ_pi]
      refine ⟨fun ⟨z, hz, hzy⟩ ↦ ?_, fun h ↦ ⟨_, (V.mem_finiteLattice_iff g _).2 h, ?_⟩⟩
      · rw [← hzy, hinv]
        exact (V.mem_finiteLattice_iff g z).1 hz
      · rw [smul_smul, Units.mul_inv, one_smul]
    rw [hpre]
    exact (isOpen_set_pi Set.finite_univ fun _ _ ↦
      FiniteAdeleRing.isOpen_integralAdeles _ _).preimage (by fun_prop)
  -- Every such `L` lies in the compact set `b⁻¹ Λ_g`, the image of `Ôⁿ` under `v ↦ b⁻¹ (F v)`.
  have hC : IsCompact ((fun v ↦ (↑b⁻¹ : 𝔸ᶠ[E]) • (F *ᵥ v)) '' O) :=
    (isCompact_univ_pi fun _ ↦
      FiniteAdeleRing.isCompact_integralAdeles (R := 𝓞 E) (K := E)).image (by fun_prop)
  refine (Submodule.finite_setOf_inf_le_le_subset hU (W.restrictScalars _) hC).subset ?_
  rintro L ⟨hLW, hlow, hup⟩
  refine ⟨fun y ⟨hy, hyW⟩ ↦ hlow ?_, hLW, fun y hy ↦ ?_⟩
  · -- `a Λ_g ∩ W ⊆ a (Λ_g ∩ W)`, since `W` is a submodule over the finite adeles.
    obtain ⟨z, hz, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hy
    refine Submodule.smul_mem_pointwise_smul _ _ _ ⟨hz, ?_⟩
    have hzW := W.smul_mem (↑a⁻¹ : 𝔸ᶠ[E]) hyW
    rwa [hinv] at hzW
  · have hby : (↑b : 𝔸ᶠ[E]) • y ∈ V.finiteLattice g :=
      hup (Submodule.smul_mem_pointwise_smul _ _ _ hy)
    refine ⟨F' *ᵥ ((↑b : 𝔸ᶠ[E]) • y), fun i _ ↦ (V.mem_finiteLattice_iff g _).1 hby i, ?_⟩
    dsimp only
    rw [hFF', hinv]

/-- **Finitely many lattices under the bounds.** For units `a, b` of `𝔸_f` and a submodule `W` of
`𝔸_fⁿ` over the finite adeles, the points `g` with `a (Λ_1 ∩ W) ⊆ Λ_g ∩ W` and
`b (Λ_g ∩ W) ⊆ Λ_1 ∩ W` give only finitely many lattices `Λ_g ∩ W`. -/
theorem finite_image_finiteLattice_inf (W : Submodule 𝔸ᶠ[E] (ι → 𝔸ᶠ[E])) {a b : 𝔸ᶠ[E]}
    (ha : IsUnit a) (hb : IsUnit b) :
    ((fun g ↦ V.finiteLattice g ⊓ W.restrictScalars _) ''
      {g : finiteAdelicUnitaryGroup E ι |
        a • (V.finiteLattice 1 ⊓ W.restrictScalars _) ≤ V.finiteLattice g ⊓ W.restrictScalars _ ∧
          b • (V.finiteLattice g ⊓ W.restrictScalars _) ≤
            V.finiteLattice 1 ⊓ W.restrictScalars _}).Finite := by
  refine (V.finite_setOf_le_finiteLattice_inf W 1 ha hb).subset ?_
  rintro _ ⟨g, ⟨hlow, hup⟩, rfl⟩
  exact ⟨inf_le_right, hlow, hup.trans inf_le_left⟩

/-! ### Locality of the lattices -/

section Cut

variable {T : Set (HeightOneSpectrum (𝓞 E))} (hT : conjPlace ⁻¹' T = T)

/-- Coordinates of `c • y` in the frame `x_f h`: first the coordinates of `y` in `x_f`, scaled by
`c`, then the action of `h⁻¹`. -/
private theorem inv_frame_mul_mulVec_smul (h : GL ι 𝔸ᶠ[E]) (c : 𝔸ᶠ[E]) (y : ι → 𝔸ᶠ[E]) :
    (↑(V.frame.2 * h)⁻¹ : Matrix ι ι 𝔸ᶠ[E]) *ᵥ (c • y) =
      (↑h⁻¹ : Matrix ι ι 𝔸ᶠ[E]) *ᵥ (c • ((↑V.frame.2⁻¹ : Matrix ι ι 𝔸ᶠ[E]) *ᵥ y)) := by
  rw [_root_.mul_inv_rev, Units.val_mul, ← mulVec_mulVec, mulVec_smul]

/-- The part `e_T y` of a vector at a set `T` of places stable under conjugation lies in the
lattice of the cut `g_T` of `g` along `T` if and only if it lies in the lattice of `g`. -/
theorem indicatorOne_smul_mem_finiteLattice_cut_iff (g : finiteAdelicUnitaryGroup E ι)
    (y : ι → 𝔸ᶠ[E]) :
    FiniteAdeleRing.indicatorOne (K := E) T • y ∈
        V.finiteLattice (finiteAdelicUnitaryGroup.cut E ι T hT g) ↔
      FiniteAdeleRing.indicatorOne (K := E) T • y ∈ V.finiteLattice g := by
  have he := FiniteAdeleRing.isIdempotentElem_indicatorOne (R := 𝓞 E) (K := E) T
  -- On parts at `T`, the inverse `(g_T)⁻¹ = (g⁻¹)_T` of the cut acts as `g⁻¹`.
  have hcoord : (↑(V.frame.2 * finiteAdelicUnitaryGroup.cut E ι T hT g)⁻¹ :
      Matrix ι ι 𝔸ᶠ[E]) *ᵥ (FiniteAdeleRing.indicatorOne (K := E) T • y) =
        (↑(V.frame.2 * g)⁻¹ : Matrix ι ι 𝔸ᶠ[E]) *ᵥ
          (FiniteAdeleRing.indicatorOne (K := E) T • y) := by
    rw [V.inv_frame_mul_mulVec_smul, V.inv_frame_mul_mulVec_smul,
      finiteAdelicUnitaryGroup.coe_cut, ← map_inv, he.val_cutGL_mulVec_smul]
  rw [mem_finiteLattice_iff, mem_finiteLattice_iff, hcoord]

/-- The part `e_{Tᶜ} y` of a vector away from a set `T` of places stable under conjugation lies in
the lattice of the cut `g_T` of `g` along `T` if and only if it lies in the lattice `Λ_1`. -/
theorem indicatorOne_compl_smul_mem_finiteLattice_cut_iff (g : finiteAdelicUnitaryGroup E ι)
    (y : ι → 𝔸ᶠ[E]) :
    FiniteAdeleRing.indicatorOne (K := E) Tᶜ • y ∈
        V.finiteLattice (finiteAdelicUnitaryGroup.cut E ι T hT g) ↔
      FiniteAdeleRing.indicatorOne (K := E) Tᶜ • y ∈ V.finiteLattice 1 := by
  have he := FiniteAdeleRing.isIdempotentElem_indicatorOne (R := 𝓞 E) (K := E) T
  -- On parts away from `T`, the inverse `(g_T)⁻¹ = (g⁻¹)_T` of the cut acts as the identity.
  have hcoord : (↑(V.frame.2 * finiteAdelicUnitaryGroup.cut E ι T hT g)⁻¹ :
      Matrix ι ι 𝔸ᶠ[E]) *ᵥ (FiniteAdeleRing.indicatorOne (K := E) Tᶜ • y) =
        (↑(V.frame.2 * ((1 : finiteAdelicUnitaryGroup E ι) : GL ι 𝔸ᶠ[E]))⁻¹ :
          Matrix ι ι 𝔸ᶠ[E]) *ᵥ (FiniteAdeleRing.indicatorOne (K := E) Tᶜ • y) := by
    rw [V.inv_frame_mul_mulVec_smul, V.inv_frame_mul_mulVec_smul,
      finiteAdelicUnitaryGroup.coe_cut, ← map_inv, ← FiniteAdeleRing.one_sub_indicatorOne,
      he.val_cutGL_mulVec_one_sub_smul, OneMemClass.coe_one, inv_one, Units.val_one, one_mulVec]
  rw [mem_finiteLattice_iff, mem_finiteLattice_iff, hcoord]

/-- **The lattices under the bounds are determined at finitely many places.** Let `T` be a set of
finite places stable under conjugation, `W` a submodule of `𝔸_fⁿ` over the finite adeles and
`a, b ∈ 𝔸_f` with `c a = e_{Tᶜ}` and `c' b = e_{Tᶜ}` for some `c, c' ∈ Ô`, that is, invertible
with integral inverse at every place outside `T`. If `a (Λ_1 ∩ W) ⊆ Λ_g ∩ W` and
`b (Λ_g ∩ W) ⊆ Λ_1 ∩ W`, then the cut `g_T` of `g` along `T` has `Λ_{g_T} ∩ W = Λ_g ∩ W`. -/
theorem finiteLattice_cut_inf_eq (W : Submodule 𝔸ᶠ[E] (ι → 𝔸ᶠ[E])) {a b : 𝔸ᶠ[E]}
    (ha : ∃ c ∈ FiniteAdeleRing.integralAdeles (𝓞 E) E, c * a = FiniteAdeleRing.indicatorOne Tᶜ)
    (hb : ∃ c ∈ FiniteAdeleRing.integralAdeles (𝓞 E) E, c * b = FiniteAdeleRing.indicatorOne Tᶜ)
    {g : finiteAdelicUnitaryGroup E ι}
    (hlow : a • (V.finiteLattice 1 ⊓ W.restrictScalars _) ≤
      V.finiteLattice g ⊓ W.restrictScalars _)
    (hup : b • (V.finiteLattice g ⊓ W.restrictScalars _) ≤
      V.finiteLattice 1 ⊓ W.restrictScalars _) :
    V.finiteLattice (finiteAdelicUnitaryGroup.cut E ι T hT g) ⊓ W.restrictScalars _ =
      V.finiteLattice g ⊓ W.restrictScalars _ := by
  set e := FiniteAdeleRing.indicatorOne (K := E) Tᶜ
  have he : IsIdempotentElem e := FiniteAdeleRing.isIdempotentElem_indicatorOne Tᶜ
  -- A bound `d (L ∩ W) ⊆ L' ∩ W` with `c d = e` for an integral `c` moves the parts `e y` of the
  -- vectors `y ∈ W` from `L` to `L'`.
  have hmove {L L' : Submodule (FiniteAdeleRing.integralAdeles (𝓞 E) E) (ι → 𝔸ᶠ[E])} {d : 𝔸ᶠ[E]}
      (hd : ∃ c ∈ FiniteAdeleRing.integralAdeles (𝓞 E) E, c * d = e)
      (hle : d • (L ⊓ W.restrictScalars _) ≤ L' ⊓ W.restrictScalars _) {y : ι → 𝔸ᶠ[E]}
      (hy : y ∈ W) (hey : e • y ∈ L) : e • y ∈ L' := by
    obtain ⟨c, hc, hcd⟩ := hd
    lift c to FiniteAdeleRing.integralAdeles (𝓞 E) E using hc
    have hdy : d • e • y ∈ L' :=
      (hle (Submodule.smul_mem_pointwise_smul _ _ _ ⟨hey, W.smul_mem e hy⟩)).1
    have h := L'.smul_mem c hdy
    rwa [Subalgebra.smul_def, smul_smul, smul_smul, hcd, he.eq] at h
  ext y
  simp only [Submodule.mem_inf, Submodule.restrictScalars_mem]
  refine and_congr_left fun hy ↦ ?_
  rw [FiniteAdeleRing.mem_iff_indicatorOne_smul_mem_and_indicatorOne_compl_smul_mem T,
    FiniteAdeleRing.mem_iff_indicatorOne_smul_mem_and_indicatorOne_compl_smul_mem T
      (L := V.finiteLattice g), V.indicatorOne_smul_mem_finiteLattice_cut_iff hT,
    V.indicatorOne_compl_smul_mem_finiteLattice_cut_iff hT]
  exact and_congr_right' ⟨hmove ha hlow hy, hmove hb hup hy⟩

end Cut

end TauCeti.FramedHermitianSpace
