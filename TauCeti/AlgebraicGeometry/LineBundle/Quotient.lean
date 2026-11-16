/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.LineBundle.Ample
public import TauCeti.AlgebraicGeometry.LineBundle.GlobalGeneration.Basic
public import TauCeti.AlgebraicGeometry.LineBundle.Power
public import TauCeti.AlgebraicGeometry.Modules.Biprod
import TauCeti.AlgebraicGeometry.LineBundle.TwistedSections
import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.FiniteType
import TauCeti.AlgebraicGeometry.Modules.Sheaf

/-!
# Global generation and quotient presentations via ample line bundles

Let `X` be a quasi-separated scheme carrying an ample line-bundle class `a`, and let `F` be a
quasi-coherent `𝒪_X`-module of finite type. Twisting `F` by sufficiently high powers `aⁿ` produces
finitely many global sections generating `F ⊗ K` for every invertible sheaf `K` of class `aⁿ`
(Grothendieck, *EGA II*, Proposition 4.5.5; Hartshorne, Theorem II.5.17; Stacks, Tag 01Q3). No
Noetherian hypothesis on `X` is needed.

Applying this to the structure sheaf `𝒪_X` shows that all sufficiently high powers of an ample
line bundle on a quasi-separated scheme are globally generated. Tensoring the resulting finite free
presentation `𝒪_X^k ↠ F ⊗ K` on the right with a line bundle `K'` of inverse class `(aⁿ)⁻¹`
exhibits `F` as a quotient of a finite direct sum `⨁_{i : Fin k} K'` of negative ample twists
(`AlgebraicGeometry.Scheme.Modules.exists_epi_biproduct_of_generatingSections`).

Covering `X` by finitely many affine nonvanishing loci `X_{s_i}` of positive powers `a^{d_i}`,
Euclidean division `n = d_i * q + r` separates `n` into a bounded remainder `r < d_i` and a large
quotient `q = n / d_i`, allowing finite generating sets of `Γ(F ⊗ L^r, X_{s_i})` to extend
simultaneously to global sections once `q` exceeds the uniform extension thresholds
(`AlgebraicGeometry.Scheme.Modules.exists_forall_ge_exists_map_eq_tmulRight_tensorPowSection`) for
all finitely many pairs `(i, r)` and assemble into global generators via
`AlgebraicGeometry.Scheme.Modules.generatingSectionsOfSpanEqTop`.

## Main declarations

* `TauCeti.AlgebraicGeometry.LineBundleClass.IsAmple.exists_forall_ge_generatingSections`:
  Serre's global generation theorem for twists of a quasi-coherent module of finite type by all
  sufficiently high powers of an ample line-bundle class.
* `TauCeti.AlgebraicGeometry.LineBundleClass.IsAmple.exists_forall_ge_isGloballyGenerated`:
  all sufficiently high powers of an ample line-bundle class are globally generated.
* `TauCeti.AlgebraicGeometry.LineBundleClass.IsAmple.exists_forall_ge_epi_biproduct`:
  every quasi-coherent module of finite type is a quotient of a finite biproduct of copies of any
  sufficiently negative power of an ample line-bundle class.

## References

* A. Grothendieck, *Éléments de géométrie algébrique. II*, Publ. Math. IHÉS **8** (1961), §4.5.
* R. Hartshorne, *Algebraic Geometry*, GTM 52, Springer, 1977, Theorem II.5.17 and
  Corollary II.5.18.
* [The Stacks Project, Tag 01Q3](https://stacks.math.columbia.edu/tag/01Q3).
-/

public section

open CategoryTheory Limits MonoidalCategory AlgebraicGeometry Opposite TopologicalSpace TauCeti

universe u

noncomputable section

namespace TauCeti.AlgebraicGeometry.LineBundleClass

open _root_.AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

/-- Euclidean division isomorphism `(F ⊗ L^r) ⊗ M^q ≅ F ⊗ L^n` when `mk M = (mk L)^d` and
`d * q + r = n`. -/
private theorem nonempty_tensor_tensorPow_iso (F : X.Modules) (L M : InvertibleSheaf X)
    {d q r n : ℕ} (hM : LineBundleClass.mk M = LineBundleClass.mk L ^ d) (hn : d * q + r = n) :
    Nonempty ((F ⊗ TauCeti.tensorPow (L.obj : X.Modules) r) ⊗
      TauCeti.tensorPow (M.obj : X.Modules) q ≅
      F ⊗ TauCeti.tensorPow (L.obj : X.Modules) n) := by
  have hclass :
      LineBundleClass.mk (InvertibleSheaf.tensorProduct (L.tensorPow r) (M.tensorPow q)) =
        LineBundleClass.mk L ^ n := by
    rw [mk_tensorProduct, mk_tensorPow, mk_tensorPow, hM, ← pow_mul, ← pow_add, add_comm, hn]
  obtain ⟨e⟩ := InvertibleSheaf.nonempty_iso_tensorPow_of_mk_eq hclass
  exact ⟨α_ F _ _ ≪≫ whiskerLeftIso F
    (tensorIso (L.tensorPowObjIso r).symm (M.tensorPowObjIso q).symm ≪≫
      (InvertibleSheaf.tensorProductObjIso (L.tensorPow r) (M.tensorPow q)).symm ≪≫ e)⟩

private theorem exists_finite_span_and_forall_ge_map_eq [QuasiSeparatedSpace X] [CompactSpace X]
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType] (L M : InvertibleSheaf X)
    (s : Γ(M.obj, ⊤)) (hU : IsAffineOpen (M.obj.nonvanishingLocus s)) (r : ℕ) :
    ∃ (k : ℕ) (g : Fin k → Γ(F ⊗ TauCeti.tensorPow (L.obj : X.Modules) r,
        M.obj.nonvanishingLocus s)) (q₀ : ℕ),
      Submodule.span Γ(X, M.obj.nonvanishingLocus s) (Set.range g) = ⊤ ∧
      ∀ q ≥ q₀, ∀ j : Fin k,
        ∃ t' : Γ((F ⊗ TauCeti.tensorPow (L.obj : X.Modules) r) ⊗
          TauCeti.tensorPow (M.obj : X.Modules) q, ⊤),
          ((F ⊗ TauCeti.tensorPow (L.obj : X.Modules) r) ⊗
            TauCeti.tensorPow (M.obj : X.Modules) q).presheaf.map
            (homOfLE (M.obj.nonvanishingLocus_le s)).op t' =
            tmulRight (F ⊗ TauCeti.tensorPow (L.obj : X.Modules) r)
              (tensorPowSection (M.obj.presheaf.map
                (homOfLE (M.obj.nonvanishingLocus_le s)).op s) q) (g j) := by
  let U := M.obj.nonvanishingLocus s
  have : (L.obj : X.Modules).IsQuasicoherent := L.isQuasicoherent_obj
  have : (L.obj : X.Modules).IsFiniteType := by
    have : (L.obj : X.Modules).IsFinitePresentation := inferInstance
    infer_instance
  have : Module.Finite Γ(X, U) Γ(F ⊗ TauCeti.tensorPow (L.obj : X.Modules) r, U) :=
    (F ⊗ TauCeti.tensorPow (L.obj : X.Modules) r).finite_sections_of_isAffineOpen U hU
  obtain ⟨k, g, hg⟩ := Module.Finite.exists_fin
    (R := Γ(X, U)) (M := Γ(F ⊗ TauCeti.tensorPow (L.obj : X.Modules) r, U))
  have htop_cpt : IsCompact (⊤ : X.Opens).1 := isCompact_univ
  have htop_qs : IsQuasiSeparated (⊤ : X.Opens).1 := isQuasiSeparated_univ
  choose qj hqj using fun j : Fin k ↦
    exists_forall_ge_exists_map_eq_tmulRight_tensorPowSection
      (F ⊗ TauCeti.tensorPow (L.obj : X.Modules) r) htop_cpt htop_qs s (g j)
  exact ⟨k, g, Finset.univ.sup qj, hg, fun q hq j ↦
    hqj j q ((Finset.le_sup (f := qj) (Finset.mem_univ j)).trans hq)⟩

/-- Local chart step for Serre's theorem: on an affine nonvanishing locus `U = X_s` of a global
section `s` of `M` with `mk M = (mk L)^d` (`d > 0`), there exist `n₀` and, for every `n ≥ n₀`,
finitely many global sections of `F ⊗ Lⁿ` whose restrictions to `U` span `Γ(F ⊗ Lⁿ, U)`. -/
private theorem exists_forall_ge_finite_global_span [QuasiSeparatedSpace X] [CompactSpace X]
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType] (L M : InvertibleSheaf X)
    {d : ℕ} (hd : 0 < d) (hM : LineBundleClass.mk M = LineBundleClass.mk L ^ d) (s : Γ(M.obj, ⊤))
    (hU : IsAffineOpen (M.obj.nonvanishingLocus s)) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀,
      ∃ (k : ℕ) (σ : Fin k → Γ(F ⊗ TauCeti.tensorPow (L.obj : X.Modules) n, ⊤)),
        Submodule.span Γ(X, M.obj.nonvanishingLocus s)
          (Set.range fun j ↦
            (F ⊗ TauCeti.tensorPow (L.obj : X.Modules) n).presheaf.map
              (M.obj.nonvanishingLocus s).leTop.op (σ j)) = ⊤ := by
  let U := M.obj.nonvanishingLocus s
  have : (L.obj : X.Modules).IsQuasicoherent := L.isQuasicoherent_obj
  choose k g q₀ hspan hext using fun r : Fin d ↦
    exists_finite_span_and_forall_ge_map_eq F L M s hU r
  have : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  let Q := Finset.univ.sup q₀
  refine ⟨d * Q, fun n hn ↦ ?_⟩
  let r : Fin d := ⟨n % d, Nat.mod_lt n hd⟩
  let q : ℕ := n / d
  have hq : Q ≤ q := (Nat.le_div_iff_mul_le hd).mpr (by linarith)
  have hqr : q₀ r ≤ q := (Finset.le_sup (f := q₀) (Finset.mem_univ r)).trans hq
  obtain ⟨Φ⟩ := nonempty_tensor_tensorPow_iso F L M hM (Nat.div_add_mod n d)
  choose t' ht' using hext r q hqr
  refine ⟨k r, fun j ↦ Φ.hom.app ⊤ (t' j), top_unique fun z _ ↦ ?_⟩
  let e₁ : Γ(F ⊗ TauCeti.tensorPow (L.obj : X.Modules) r, U) ≃ₗ[Γ(X, U)]
      Γ((F ⊗ TauCeti.tensorPow (L.obj : X.Modules) r) ⊗
        TauCeti.tensorPow (M.obj : X.Modules) q, U) :=
    LinearEquiv.ofBijective
      (tmulRight (F ⊗ TauCeti.tensorPow (L.obj : X.Modules) r)
        (tensorPowSection (M.obj.presheaf.map (homOfLE (M.obj.nonvanishingLocus_le s)).op s) q))
      (bijective_tmulRight_tensorPowSection_of_le_nonvanishingLocus
        (F ⊗ TauCeti.tensorPow (L.obj : X.Modules) r) _
        (by rw [nonvanishingLocus_map]; exact le_inf le_rfl le_rfl) q)
  let e₂ := sectionsLinearEquiv Φ U
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun Γ(X, U)).mp
    (hspan r ▸ Submodule.mem_top (x := e₁.symm (e₂.symm z)))
  refine (Submodule.mem_span_range_iff_exists_fun Γ(X, U)).mpr ⟨c, ?_⟩
  have hz : z = e₂ (e₁ (∑ j, c j • g r j)) := by rw [hc, e₁.apply_symm_apply, e₂.apply_symm_apply]
  rw [hz, map_sum, map_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [LinearEquiv.map_smul, LinearEquiv.map_smul]
  congr 1
  have hle : U.leTop = homOfLE (M.obj.nonvanishingLocus_le s) := rfl
  have hnat : Φ.hom.app U
      (((F ⊗ TauCeti.tensorPow (L.obj : X.Modules) r) ⊗
        TauCeti.tensorPow (M.obj : X.Modules) q).presheaf.map U.leTop.op (t' j)) =
      (F ⊗ TauCeti.tensorPow (L.obj : X.Modules) n).presheaf.map U.leTop.op
        (Φ.hom.app ⊤ (t' j)) :=
    Φ.hom.mapPresheaf.naturality_apply U.leTop.op (t' j)
  dsimp only
  rw [sectionsLinearEquiv_apply, LinearEquiv.ofBijective_apply, ← ht' j, ← hle, hnat]

/-- **Serre's global generation theorem** (EGA II, Proposition 4.5.5; Stacks, Tag 01Q3): on a
quasi-separated scheme `X`, let `a` be an ample line-bundle class and `F` a quasi-coherent
`𝒪_X`-module of finite type. There exists `n₀ : ℕ` such that for every `n ≥ n₀` and every line
bundle `K` of class `aⁿ`, `F ⊗ K` is generated by finitely many global sections. -/
theorem IsAmple.exists_forall_ge_generatingSections [QuasiSeparatedSpace X]
    {a : LineBundleClass X} (ha : a.IsAmple) (F : X.Modules)
    [F.IsQuasicoherent] [F.IsFiniteType] :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ K : InvertibleSheaf X, LineBundleClass.mk K = a ^ n →
      ∃ G : (F ⊗ (K.obj : X.Modules)).GeneratingSections, G.IsFiniteType := by
  have := ha.compactSpace
  obtain ⟨L, rfl⟩ := mk_surjective a
  have hLqc : (L.obj : X.Modules).IsQuasicoherent := L.isQuasicoherent_obj
  choose dx hdx hMx using fun x : X ↦ ha.exists_pos_forall_mk_eq x
  let Mx (x : X) : InvertibleSheaf X := L.tensorPow (dx x)
  choose sx hsx hAffx using fun x : X ↦ hMx x (Mx x) (mk_tensorPow L (dx x))
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun x : X ↦ ((Mx x).obj.nonvanishingLocus (sx x) : Set X))
    (fun x ↦ ((Mx x).obj.nonvanishingLocus (sx x)).isOpen)
    (fun x _ ↦ Set.mem_iUnion.mpr ⟨x, hsx x⟩)
  let U (i : t) : X.Opens := (Mx i).obj.nonvanishingLocus (sx i)
  have hcover : ⨆ i : t, U i = ⊤ := top_unique fun x _ ↦ by
    obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ x))
    exact Opens.mem_iSup.mpr ⟨⟨y, hy⟩, hxy⟩
  choose n₀ hn₀ using fun i : t ↦
    exists_forall_ge_finite_global_span F L (Mx i) (hdx i) (mk_tensorPow L (dx i)) (sx i) (hAffx i)
  refine ⟨t.attach.sup n₀, fun n hn K hK ↦ ?_⟩
  choose ki σi hspani using fun i : t ↦
    hn₀ i n ((Finset.le_sup (f := n₀) (Finset.mem_attach t i)).trans hn)
  let σ : (Σ i : t, Fin (ki i)) → Γ(F ⊗ TauCeti.tensorPow (L.obj : X.Modules) n, ⊤) :=
    fun p ↦ σi p.1 p.2
  have hspan (i : t) : Submodule.span Γ(X, U i)
      (Set.range fun p : Σ i : t, Fin (ki i) ↦
        (F ⊗ TauCeti.tensorPow (L.obj : X.Modules) n).presheaf.map (U i).leTop.op (σ p)) = ⊤ :=
    top_unique (by
      rw [← hspani i]
      refine Submodule.span_mono ?_
      rintro _ ⟨j, rfl⟩
      exact ⟨⟨i, j⟩, rfl⟩)
  let G₀ := generatingSectionsOfSpanEqTop (F ⊗ TauCeti.tensorPow (L.obj : X.Modules) n)
    (fun i : t ↦ hAffx i) hcover σ hspan
  have hG₀ : G₀.IsFiniteType := inferInstance
  obtain ⟨e⟩ := InvertibleSheaf.nonempty_iso_tensorPow_of_mk_eq hK
  exact ⟨SheafOfModules.GeneratingSections.equivOfIso
    (toSheafOfModulesIso (whiskerLeftIso F e.symm)) G₀, { finite := hG₀.finite }⟩

/-- All sufficiently high powers of an ample line-bundle class on a quasi-separated scheme are
globally generated. -/
theorem IsAmple.exists_forall_ge_isGloballyGenerated [QuasiSeparatedSpace X]
    {a : LineBundleClass X} (ha : a.IsAmple) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ K : InvertibleSheaf X, LineBundleClass.mk K = a ^ n →
      K.IsGloballyGenerated := by
  obtain ⟨n₀, hn₀⟩ := ha.exists_forall_ge_generatingSections (𝟙_ X.Modules)
  refine ⟨n₀, fun n hn K hK ↦
    InvertibleSheaf.isGloballyGenerated_iff_nonempty_generatingSections.mpr ?_⟩
  obtain ⟨G, -⟩ := hn₀ n hn K hK
  exact ⟨SheafOfModules.GeneratingSections.equivOfIso
    (toSheafOfModulesIso (λ_ (K.obj : X.Modules))) G⟩

/-- **Quotient presentation by negative ample twists** (Hartshorne, Corollary II.5.18): on a
quasi-separated scheme `X`, let `a` be an ample line-bundle class and `F` a quasi-coherent
`𝒪_X`-module of finite type. There exists `n₀ : ℕ` such that for every `n ≥ n₀` and every line
bundle `K` of class `(aⁿ)⁻¹`, `F` is a quotient of a finite biproduct of copies of `K`. -/
theorem IsAmple.exists_forall_ge_epi_biproduct [QuasiSeparatedSpace X]
    {a : LineBundleClass X} (ha : a.IsAmple) (F : X.Modules)
    [F.IsQuasicoherent] [F.IsFiniteType] :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ K : InvertibleSheaf X, LineBundleClass.mk K = (a ^ n)⁻¹ →
      ∃ (k : ℕ) (p : (⨁ fun _ : Fin k ↦ (K.obj : X.Modules)) ⟶ F), Epi p := by
  obtain ⟨n₀, hn₀⟩ := ha.exists_forall_ge_generatingSections F
  refine ⟨n₀, fun n hn K hK ↦ ?_⟩
  obtain ⟨P, hP⟩ := mk_surjective (a ^ n)
  obtain ⟨G, hG⟩ := hn₀ n hn P hP
  have hPK : LineBundleClass.mk (InvertibleSheaf.tensorProduct P K) = 1 := by
    rw [mk_tensorProduct, hP, hK, mul_inv_cancel]
  obtain ⟨e₀⟩ := mk_eq_one_iff.mp hPK
  exact exists_epi_biproduct_of_generatingSections
    ((InvertibleSheaf.tensorProductObjIso P K).symm ≪≫ isoOfSheafIso X e₀) G

end TauCeti.AlgebraicGeometry.LineBundleClass

end
